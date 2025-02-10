import { RacketProcess } from './racketprocess';
import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';
import { removeForgeComments, getFailingTestsData, getFailingTestData, combineTestsWithModel } from './forge-utilities';
import { ConceptualMutator } from './conceptualmutator';
import { LogLevel, Logger, Event } from './logger';
import { SymmetricEncryptor } from './encryption-util';
import * as os from 'os';
import { tempFile } from './gen-utilities';

export class RunResult {

	constructor(stderr = "", stdout = "", runsource = "") {
		this.stderr = stderr;
		this.stdout = stdout;
		this.runsource = runsource;
	}
	stderr: string;
	stdout: string;
	runsource: string;
}

// The maximum number of hints to display to the user for a single run.
const MAX_HINT = 3;

const NOT_ENABLED_MESSAGE = "Sorry! Toadus Ponens is not available for this assignment. Please contact course staff if you believe this is an error.";
const CONSISTENCY_MESSAGE = `🎉 Your tests are all consistent with the assignment specification! 🎉 Just because your tests are consistent, however, does not mean they thoroughly explore the problem space.`;
const ANALYZED_CONSISTENCY_MESSAGE = `🎉 Analyzed tests are all consistent with the assignment specification!
										 However, the tests we could not analyze are either 
										 inconsistent with or test behavior not specified by the problem statement.`;

const TIMEOUT_MESSAGE = "Toadus Ponens timed out.";

export class HintGenerator {

	private SOMETHING_WENT_WRONG = "Something went wrong during Toadus Ponens analysis. While I will still make a best effort to provide useful feedback, consider examining your tests with course staff. You may find it useful to share the the VSCode Error log with them. You can access it as follows: Ctrl-shift-p or cmd-shift-p -> Search Show Logs -> Extension Host";

	    // Read WHEATSTORE URL from VS Code settings
	static get WHEATSTORE(): string {
		const config = vscode.workspace.getConfiguration('forge');
		return config.get<string>('toadusSource', 'https://csci1710.github.io/2025/toadusponensfiles');
	}

	logger: Logger;
	encryptor: SymmetricEncryptor = new SymmetricEncryptor();
	forgeOutput: vscode.OutputChannel;

	formurl = "https://forms.gle/t2imxLGNC7Yqpo6GA"
	public AMBIGUOUS_TEST_MESSAGE = `Analyzed test(s) examine behaviors that are not clearly defined in the problem specification. They are not necessarily incorrect, but I cannot provide feedback around them.\nIf you disagree with this, fill out this form: ${this.formurl}`;

	mutationStrategy: string;
	thoroughnessStrategy: string;

	step_num : number = 0;

	constructor(logger: Logger, output: vscode.OutputChannel) {
		this.logger = logger;
		this.forgeOutput = output;

		const currentSettings = vscode.workspace.getConfiguration('forge');
		this.mutationStrategy = String(currentSettings.get('feedbackStrategy'));
		this.thoroughnessStrategy = String(currentSettings.get('thoroughnessFeedback'));
	}

	public async generateHints(studentTests: string, testFileName: string): Promise<string> {

		this.logger.log_payload({ 'feedbackstrategy': this.mutationStrategy }, LogLevel.INFO, Event.ASSISTANCE_REQUEST);

		studentTests = studentTests.replace(/\r/g, "\n");
		const w = await this.getWheat(testFileName);

		if (w === "") {
			vscode.window.showErrorMessage("Toadus : Network error. Terminating run.");
			return "";
		}
		else if (w === NOT_ENABLED_MESSAGE) {
			vscode.window.showErrorMessage(NOT_ENABLED_MESSAGE);
			return "";
		}

		this.forgeOutput.appendLine(`🐸 Step ${++this.step_num}: Analyzing your tests for validity.`);


		// Step 1: Download the wheat, and run the STUDENT tests against it.
		const run_result = await this.runTestsAgainstModelWithTimeout(studentTests, w);
		const w_o = run_result.stderr;
		const source_text = run_result.runsource;
		

		// Step 2: If all the tests pass the wheat, we know they are consistent with the problem specification.
		// We MAY want to generate feedback around thoroughness.
		if (this.isConsistent(w_o)) {

			if (this.thoroughnessStrategy == "Off") {
				return CONSISTENCY_MESSAGE;
			}
			this.forgeOutput.appendLine(CONSISTENCY_MESSAGE);
			// Otherwise, generate feedback around thoroughness.
			const thoroughness_candidates = await this.generateThoroughnessFeedback(w, studentTests, w_o, testFileName, source_text);
			return this.generateThoroughnessFeedbackFromCandidates(thoroughness_candidates);

		}
		// Step 3: Tests may fail for one of two reasons -- 
		// a test ERROR vs a test FAIL. We need to distinguish between these two cases.

		// First, we deal with test errors.
		// We look for patterns in the output to check if any tests actually failed.
		const failingTests = getFailingTestsData(w_o);
		const failingTestNames = failingTests.map((testData) => testData.name);

		// If not, just return a message that we found a runtime or syntax error in the tests.
		if (failingTestNames.length == 0) {
			const noTestFound = `I found a runtime or syntax error in your tests:\n ${w_o}`;
			return noTestFound;
		}

		// Step 4: Some tests *have* failed against the wheat.
		// Now there are two possibilities here -- the failing tests explore
		// ambiguous/undefined behavior, or they are inconsistent with the problem specification.
		// In order to determine this, we need to generate a conceptual mutant.

		// An intesting question is: Can we *first* run comprehensive -- but if the mutant is 
		// not satisfiable, then run per test? This would be a hybrid strategy.
		try {

			// There are two strategies for generating feedback -- comprehensive and per test.
			if (this.mutationStrategy == "Per Test") {
				// The per-test strategy is super granular and low performance.
				// It generates feedback about *each* failing test by generating a conceptual
				// mutant per failing test.
				const per_test_hints = await this.runPerTestStrategy(w, w_o, studentTests, testFileName, source_text);

				// Now need to annotate per test hints with the test name.
				this.forgeOutput.appendLine(`🐸 Step ${++this.step_num}: I suspect that the following test(s) may be inconsistent with the problem specification.`);
				this.forgeOutput.appendLine(`Generating feedback around these tests ⌛`);


				let composite_hint = "";
				let non_ambiguous_failures = 0;
				let ambiguous_failures = 0;
				// Now we need to choose a hint per test. But what about ambiguous tests? This is where it happens?
				for (const test in per_test_hints) {

					let hint = this.generateHintFromCandidates(per_test_hints[test]);
					if (hint == "") {
						ambiguous_failures++;
						hint = this.recordAmbiguousTest(testFileName, studentTests, w_o);
					}
					else {
						non_ambiguous_failures++;
					}

					composite_hint += `\n${test} : ${hint}\n`;
				}

				if (non_ambiguous_failures == 0 && this.thoroughnessStrategy != "Off") {

					if (ambiguous_failures > 0) {
						this.forgeOutput.appendLine(`🚨: Some analyzed tests examine behavior not specified by the problem statement.`);
					}
					this.forgeOutput.appendLine(`🐸 Since none of the analyzed tests are obviously
					inconsistent with the problem specification, I will now analyze the thoroughness of your test-suite. ⌛`);
					const thoroughness_candidates = await this.generateThoroughnessFeedback(w, studentTests, w_o, testFileName, source_text);
					return this.generateThoroughnessFeedbackFromCandidates(thoroughness_candidates);
				}


				return composite_hint;
			}

			else if (this.mutationStrategy == "Comprehensive") {
				// The comprehensive strategy is high performance and low granularity.
				// It generates a single conceptual mutant that is consistent with all failing tests.
				// It then generates feedback around this single mutant.




				const hints = await this.runComprehensiveStrategy(w, w_o, source_text, studentTests, testFileName);

				//// THis is hacky ///
				const hintSet = new Set(hints);
				const noHint = hintSet.size == 0;
				const onlyAmbiguous = hintSet.size == 1 && hintSet.has(this.AMBIGUOUS_TEST_MESSAGE);
				const meaningfulHints = !noHint && !onlyAmbiguous;

				if (meaningfulHints || this.thoroughnessStrategy == "Off") {
					return this.generateHintFromCandidates(hints);
				}
				else if (onlyAmbiguous) {
					this.forgeOutput.appendLine(this.AMBIGUOUS_TEST_MESSAGE);
				}
				else {
					this.forgeOutput.appendLine(ANALYZED_CONSISTENCY_MESSAGE);
				}

				// Now we need to generate feedback around thoroughness,
				// but this may be complicated since some tests may be ambiguous.
				// OR incorrect but not analyzable.
				const thoroughness_candidates = await this.generateThoroughnessFeedback(w, studentTests, w_o, testFileName, source_text);
				return this.generateThoroughnessFeedbackFromCandidates(thoroughness_candidates);
			}
			else {
				return "Something was wrong in the extension settings. toadusponens.feedbackStrategy must be either 'Comprehensive' or 'Per Test'";
			}
		}
		catch (e) {
			vscode.window.showErrorMessage(this.SOMETHING_WENT_WRONG);
			return this.SOMETHING_WENT_WRONG;
		}
	}



	isConsistent(w_o: string): boolean {
		const lines = w_o.split("\n");
		const filteredLines = lines.filter((line) => !line.startsWith("Warning:"));
		return filteredLines.join('').trim().length == 0;
	}


	chooseN(arr: any[], n: number): any[] {
		const randomElements: any[] = [];
		const maxElements = Math.min(arr.length, n);
		for (let i = 0; i < maxElements; i++) {
			const randomIndex = Math.floor(Math.random() * arr.length);
			randomElements.push(arr[randomIndex]);
			arr.splice(randomIndex, 1);
		}
		return randomElements;
	}


	generateHintFromCandidates(hint_candidates: string[]): string {

		if (hint_candidates.length == 0) {
			return "";
		}

		const chosen_hints = this.chooseN(hint_candidates, MAX_HINT)
			.map(hint => `🐸💡 ${hint}`)
			.join("\n");

		return chosen_hints;
	}


	generateThoroughnessFeedbackFromCandidates(thoroughness_hints: string[]): string {
		if (thoroughness_hints.length == 0) {
			return "I could not generate a hint to help evaluate test thoroughness. It's important to remember that this doesn't automatically mean the tests are exhaustive or explore every aspect of the problem.";
		}

		const feedback = this.chooseN(thoroughness_hints, MAX_HINT)
			.map(hint => `🐸 🗯️ ${hint}`)
			.join("\n");

		return feedback;
	}



	/**
	 * Implements the comprehensive mutation strategy. 
	 * This strategy generates a single conceptual mutant that is consistent with all failing tests.
	 */
	private async runComprehensiveStrategy(w: string, w_o: string, source_text: string, studentTests: string, testFileName: string,): Promise<string[]> {

		const mutator = new ConceptualMutator(w, studentTests, w_o, testFileName, source_text);

		// Start by generating a conceptual mutant that 
		// is consistent with all failing tests.
		mutator.mutateToFailingTests();

		const inconsistent_tests = mutator.inconsistent_tests;

		// These are the tests used to generate feedback.
		const assessed_tests = inconsistent_tests.join("\n");

		const skipped_test_count = mutator.skipped_tests.length;
		if (skipped_test_count > 0) {
			// These are the tests that Toadus Ponens could not analyze.
			const skipped_tests = "Could not analyze the following tests:\n" + mutator.get_skipped_tests_as_string();
			this.forgeOutput.appendLine(skipped_tests);
		}



		// IF there are no inconsistent tests, everything is good right?
		if (inconsistent_tests.length == 0) {

			this.forgeOutput.appendLine(`The remaining tests seem consistent with the problem,
				 but may test behavior that is not clearly defined in the problem specification.
				 You may want to change settings to 'Per Test' to get individual feedback around these tests.`);

			// SP: TODO: Figure out what we should do here. 
			return [];
		}


		this.forgeOutput.appendLine(`🐸 Step ${++this.step_num}: The following ${mutator.inconsistent_tests.length} test(s) MAY be inconsistent 
										with the assignment specification:\n ${assessed_tests}\n\nAnalyzing these tests further ⌛\n`);


		// So now we have a conceptual mutant that is consistent with all failing tests.
		// We need to RUN this mutant against the autograder tests to see if it passes.
		// Then, we can generate feedback around this mutant.
		let hints = [];
		try {

			// First get the mutant as a program
			const mutant = mutator.getMutantAsString();

			hints = await this.tryGetHintsFromMutantFailures(
				testFileName,
				mutant,
				mutator.student_tests,
				mutator.forge_output);
		}
		catch (e) {
			vscode.window.showErrorMessage(this.SOMETHING_WENT_WRONG);
			this.forgeOutput.appendLine(e.message);
			return [this.SOMETHING_WENT_WRONG];
		}

		if (hints.length == 0) {
			// One lost piece of information is that students do not know
			// *which* tests are ambiguous. We lose this granularity with a comprehensive mutation strategy.
			return [this.recordAmbiguousTest(testFileName, studentTests, mutator.forge_output)];
		}
		return hints;

	}


	/**
	 * Implements the per-test mutation strategy. 
	 * This strategy generates a conceptual mutant per failing test and generates feedback around each mutant.
	 */
	private async runPerTestStrategy(w: string, w_o: string, studentTests: string, testFileName: string, source_text: string): Promise<any> {


		const per_test_hints = {};
		const lines = w_o.split("\n");

		for (const outputline of lines) {
			const testData = getFailingTestData(outputline);
			if (testData == undefined) {
				continue;
			}
			const tn = testData.name;
			if (tn == "") {
				continue;
			}

			const lineMutator = new ConceptualMutator(w, studentTests, outputline, testFileName, source_text, 1);
			lineMutator.mutateToFailingTests();

			const mutant = lineMutator.getMutantAsString();
			const hints = await this.tryGetHintsFromMutantFailures(testFileName, mutant, lineMutator.student_tests, outputline);
			per_test_hints[tn] = hints;


			/*
				We should do something about the ambiguous tests here


			*/

		}

		return per_test_hints;

	}

	
	recordAmbiguousTest(testFileName: string, studentTests: string, forge_output: string): string {
		const payload = {

			"studentTests": studentTests,
			"wheat_output": forge_output,
			"testFile": testFileName
		};
		this.logger.log_payload(payload, LogLevel.INFO, Event.AMBIGUOUS_TEST);
		return this.AMBIGUOUS_TEST_MESSAGE;

	}



	private runTestsAgainstModelWithTimeout(tests: string, model: string, timeout: number = 60000): Promise<RunResult> {
		// This function is a wrapper around runTestsAgainstModel that adds a timeout.
		return new Promise((resolve, reject) => {
			// Set a timeout to reject the promise if the operation takes too long
			const timeoutId = setTimeout(() => {
				// Show a timeout message in the VS Code error window
				vscode.window.showErrorMessage(TIMEOUT_MESSAGE);
				// Resolve the promise with a timeout result if the operation takes too long
				resolve(new RunResult(TIMEOUT_MESSAGE, TIMEOUT_MESSAGE, tests));
			}, timeout);
	
			// Call the runTestsAgainstModel function and handle its result
			this.runTestsAgainstModel(tests, model).then(result => {
				// Clear the timeout if the operation completes successfully
				clearTimeout(timeoutId);
				// Resolve the promise with the result of runTestsAgainstModel
				resolve(result);
			}).catch(error => {
				// Clear the timeout if the operation fails
				clearTimeout(timeoutId);
				// Reject the promise with the error from runTestsAgainstModel
				reject(error);
			});
		});
	}




	private async runTestsAgainstModel(tests: string, model: string): Promise<RunResult> {

		const forgeEvalDiagnostics = vscode.languages.createDiagnosticCollection('Forge Eval');
		const racket: RacketProcess = RacketProcess.getInstance(forgeEvalDiagnostics, this.forgeOutput);


		const toRun = combineTestsWithModel(model, tests);
		const LAUNCH_FAILURE_ERR = "Could not run Toadus Ponens process.";

		const runresult = new RunResult("", "", toRun);

		// Write the contents of toRun to a temporary file
		const tempFilePath = tempFile();
		try {
			fs.writeFileSync(tempFilePath, toRun);

			let stdoutListener = (data: string) => { runresult.stdout += data; };
			let stderrListener = (data: string) => { runresult.stderr += data; };
			let promise = racket.runFile(tempFilePath,stdoutListener, stderrListener);

			// Now we want to await the promise, but want different behavior based on the result.
			await promise;

		} catch (e) {
			vscode.window.showErrorMessage(`Toadus Ponens run failed, perhaps be because VS Code did not have permission to write a file to your OS temp folder (${os.tmpdir()}). Consult the Toadus Ponens guide for how to modify this. Full error message : ${e}`);
			runresult.stderr = e;
		}
		finally {
			// Delete the temporary file 
			fs.unlinkSync(tempFilePath);
		}
		return runresult;
	}


	private async downloadFile(url: string): Promise<string> {

		const response = await fetch(url);
		if (response.ok) {
			const t = await response.text();
			return this.encryptor.decrypt(t);
		}

		this.logger.log_payload({ "url": url }, LogLevel.ERROR, Event.FILE_DOWNLOAD);
		if (response.status === 404) {
			vscode.window.showErrorMessage(NOT_ENABLED_MESSAGE);
			return NOT_ENABLED_MESSAGE;
		}
		else {
			vscode.window.showErrorMessage(`Toadus : Network error ${response.status} ${response.statusText}`);
			return ""; 			// ERROR
		}
	}

	private async getWheat(testFileName: string): Promise<string> {

		const wheatName = path.parse(testFileName.replace('.test.frg', '.wheat')).base;
		const wheatURI = `${HintGenerator.WHEATSTORE}/${wheatName}`;
		const wheat = await this.downloadFile(wheatURI);
		return removeForgeComments(wheat);
	}

	private async getAutograderTests(testFileName: string): Promise<string> {
		const graderName = path.parse(testFileName.replace('.test.frg', '.grader')).base;
		const graderURI = `${HintGenerator.WHEATSTORE}/${graderName}`;
		let f = await this.downloadFile(graderURI);

		//// TODO: Remove. A hack because I'm lazy for testing ///
		// Replace all instances of 'is theorem' with 'is checked' in the autograder tests.

		f = f.replace(/(is theorem)/g, "is checked");
		///
		return f;
	}

	private async getHintMap(testFileName: string): Promise<any> {
		const graderName = path.parse(testFileName.replace('.test.frg', '.grader.json')).base;
		const graderURI = `${HintGenerator.WHEATSTORE}/${graderName}`;
		const jsonString = await this.downloadFile(graderURI);
		try {
			const jsonObject = JSON.parse(jsonString);
			return jsonObject;
		}
		catch {
			return {};
		}
	}


	private async tryGetFailingHintsFromAutograderOutput(ag_output: string, testFileName: string): Promise<string[]> {
		if (ag_output == "") {
			return [];
		}
		const failingTests = getFailingTestsData(ag_output);
		const tNames = failingTests.map((testData) => testData.name);
		const hint_map = await this.getHintMap(testFileName);

		const issues = tNames.filter((tName) => !(tName in hint_map));
		if (issues.length > 0) {
			vscode.window.showErrorMessage("Something went wrong during Toadus Ponens analysis. While I will still make a best effort to provide useful feedback, consider examining your tests with course staff.");
		}


		const hint_candidates = tNames.filter((tName) => tName in hint_map)
			.map((tName) => hint_map[tName]);
		return hint_candidates;
	}


	/**
	 * Runs a mutant program against the autograder tests and extracts hints from the output.
	 * @param testFileName 
	 * @param mutant 
	 * @param student_preds 
	 * @param w_o 
	 * @param event 
	 * @returns Candidate hints.
	 */
	async tryGetHintsFromMutantFailures(testFileName: string, mutant: string, student_preds: string, w_o: string, event: Event = Event.CONCEPTUAL_MUTANT): Promise<string[]> {


		// TODO: This isn't always for thoroughness!


		// Step 1. Log what we are doing.
		const payload = {
			"testFileName": testFileName,
			"assignment": testFileName.replace('.test.frg', ''),
			"student_preds": student_preds, // THIS IS NOW ALL STUDENT TESTS.
			"test_failure_message": w_o,
			"conceptual_mutant": mutant
		};
		this.logger.log_payload(payload, LogLevel.INFO, event);

		// Step 2. Download the autograder tests.
		const autograderTests = await this.getAutograderTests(testFileName);






		// Step 3. Run the mutant against the autograder tests.
		const ag_meta = await this.runTestsAgainstModelWithTimeout(autograderTests, mutant);
		const ag_output = ag_meta.stderr;

		if (ag_output == TIMEOUT_MESSAGE) {
			return [TIMEOUT_MESSAGE];
		}


		// Step 4. Extract hints from the output.
		return await this.tryGetFailingHintsFromAutograderOutput(ag_output, testFileName);
	}

	private async tryGetPassingHintsFromAutograderOutput(ag_output: string, testFileName: string): Promise<string[]> {

		// ENSURE THAT AUTOGRADER TESTS HAVE UNAMBIGUOUS NAMES
		// SO TEST-EXPECT ONLY

		const failed_tests = getFailingTestsData(ag_output).map((testData) => testData.name);
		const hint_map = await this.getHintMap(testFileName);

		const test_names = Object.keys(hint_map);
		const missingTests = test_names.filter(x => !failed_tests.includes(x));
		const hint_candidates = missingTests.map((tName) => hint_map[tName]);
		return hint_candidates;
	}

	async tryGetHintsFromMutantPasses(testFileName: string, mutant: string, student_preds: string): Promise<string[]> {


		const payload = {
			"testFileName": testFileName,
			"assignment": testFileName.replace('.test.frg', ''),
			"student_preds": student_preds, // This is now all student tests.
			"conceptual_mutant": mutant
		};
		this.logger.log_payload(payload, LogLevel.INFO, Event.THOROUGHNESS_MUTANT);

		const autograderTests = await this.getAutograderTests(testFileName);
		const ag_meta = await this.runTestsAgainstModelWithTimeout(autograderTests, mutant);
		const ag_output = ag_meta.stderr;

		if (ag_output == TIMEOUT_MESSAGE) {
			return [TIMEOUT_MESSAGE];
		}

		return await this.tryGetPassingHintsFromAutograderOutput(ag_output, testFileName);
	}

	async generateThoroughnessFeedback(wheat: string, student_tests: string, forge_output: string, test_file_name: string, source_text: string): Promise<string[]> {


		this.forgeOutput.appendLine(`🐸 Step ${++this.step_num}: Assessing the thoroughness of your test-suite.`);
		this.forgeOutput.show();

		/*
			- For each test-suite, identify the predicate being tested.
			- For each test in the suite.
				- Produce a predicate that characterizes the test.
				- Exclude these predicates from the predicate under test.
		*/


		// We will use this mutator to generate a mutant that is INconsistent with all tests of inclusion.
		const inclusion_mutator = new ConceptualMutator(wheat, student_tests, forge_output, test_file_name, source_text);

		// We will use this mutator to generate a mutant that is consistent with all tests of exclusion.
		const exclusion_mutator = new ConceptualMutator(wheat, student_tests, forge_output, test_file_name, source_text);

		// We use this mutator to detect positive tests in the Autograder test suite.
		// Ideally, we should change this.
		const null_mutator = new ConceptualMutator(wheat, student_tests, forge_output, test_file_name, source_text);


		const num_inclusion_mutations = inclusion_mutator.mutateToExcludeInclusionTests();
		const num_exclusion_mutations = exclusion_mutator.mutatefromExclusionTestIntersection();
		null_mutator.mutateToVaccuity();


		const skipped_tests = inclusion_mutator.get_skipped_tests_as_string() + exclusion_mutator.get_skipped_tests_as_string();
		this.forgeOutput.appendLine(skipped_tests);

		const tests_analyzed = num_inclusion_mutations + num_exclusion_mutations;

		// There should be one mutation per considered, consistent test
		this.forgeOutput.appendLine(`🐸 Step ${++this.step_num}: Here are some ideas for scenarios NOT covered by the ${tests_analyzed} tests analyzed. ⌛\n`);
		this.forgeOutput.show();
		try {

			const mutantOfInclusion = inclusion_mutator.getMutantAsString();
			const mutantOfExclusion = exclusion_mutator.getMutantAsString();
			const vaccuousMutant = null_mutator.getMutantAsString();

			// All those tests that were not covered by positive test cases
			const thoroughness_hints = await this.tryGetHintsFromMutantPasses(inclusion_mutator.test_file_name, mutantOfInclusion, inclusion_mutator.student_tests);

			// All those tests covered by negative test cases (and all positive tests)
			const negative_covered_hints_and_pos = await this.tryGetHintsFromMutantPasses(exclusion_mutator.test_file_name, mutantOfExclusion, exclusion_mutator.student_tests);

			// (in theory) all positive test cases. TODO: There may be scenarios were this is buggy, so we need to think about it.
			const positive_test_hints = await this.tryGetHintsFromMutantPasses(null_mutator.test_file_name, vaccuousMutant, null_mutator.student_tests);
			const negative_covered_hints = negative_covered_hints_and_pos.filter(hint => !positive_test_hints.includes(hint));


			const difference = thoroughness_hints.filter(hint => !negative_covered_hints.includes(hint));
			return difference;

		}
		catch (e) {
			vscode.window.showErrorMessage(this.SOMETHING_WENT_WRONG);
			this.forgeOutput.appendLine(e.message);
			return [this.SOMETHING_WENT_WRONG];
		}
	}

}