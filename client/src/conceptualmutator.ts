import { combineTestsWithModel } from './forge-utilities';
import { getFailingTestData } from './forge-utilities';


import {
	ForgeUtil,
	Block, SyntaxNode,
	Sig, Predicate, Function,
	Test, AssertionTest, QuantifiedAssertionTest, Example, SatisfiabilityAssertionTest,
	ConsistencyAssertionTest, Expr,
	Formula
} from "forge-toadus-parser";


const negationRegex = /(not|!)\s*(\b\w+\b)/;



class SkippedTest {
	constructor(public test: string, public reason: string) { }
}


// TODO: These feel like something I should be able to get AWAY from using.
function isAssertionTest(t: any): t is AssertionTest {
	return t && typeof t === 'object' && 
			'prop' in t && 'pred' in t 
			&& !('consistent' in t) && !('quantifier' in t);
}

function isQuantifiedAssertionTest(t: any): t is QuantifiedAssertionTest {
	return t && typeof t === 'object' && 'prop' in t && 'pred' in t && 'quantifier' in t;
}

function isExample(t: any): t is Example {
	return t && (typeof t === 'object') && ('testExpr' in t);
}

function isConsistencyAssertionTest(t: any): t is ConsistencyAssertionTest {
	return t && (typeof t === 'object') && ('consistent' in t);
}

function isTestExpect(t: any): t is Test {
	return t && (typeof t === 'object') && ('name' in t) && ('check' in t);
}

function isSatisfiabilityAssertionTest(t: any): t is SatisfiabilityAssertionTest {
	return t && (typeof t === 'object') && ('check' in t)
			&& !isTestExpect(t) && !isConsistencyAssertionTest(t)
			&& !isAssertionTest(t) && !isQuantifiedAssertionTest(t);
}



function getExprFromBracesIfAny(s: string): string {

	const scleaned = s.trim();
	if (scleaned.startsWith("{") && scleaned.endsWith("}")) {
		return scleaned.substring(1, scleaned.length - 1);
	}
	return scleaned;
}


// TODO: Check how params get constructed here!
class HydratedPredicate {
	constructor(
		public name: string,
		public params: Record<string, string>,
		public body: string
	) {

	}

	declParams(): string {
		const paramStrings = [];
		for (const [name, type] of Object.entries(this.params)) {
			paramStrings.push(`${name}: ${type}`);
		}

		if (paramStrings.length == 0) {
			return "";
		}

		const paramStringsJoined = paramStrings.join(", ");
		return "[" + paramStringsJoined + "]";
	}

	callParams(): string {
		const paramStrings = [];
		for (const [name, type] of Object.entries(this.params)) {
			paramStrings.push(name);
		}

		if (paramStrings.length == 0) {
			return "";
		}

		const paramStringsJoined = paramStrings.join(", ");
		return "[" + paramStringsJoined + "]";
	}
}

/*
    Row numbers are 1-indexed.
    Column numbers are 0-indexed.
*/
function get_text_block(fromRow: number, toRow: number, fromColumn: number, toColumn: number, text: string): string {
    const lines = text.split("\n");
    let block = "";
    const sameRow = fromRow == toRow;

    for (let i = fromRow; i <= toRow; i++) {
        const line = lines[i - 1]; // Row numbers are 1-indexed, so adjust by subtracting 1

        if (i == fromRow) {
            if (sameRow) {
                // If the block is within the same row, take the substring from fromColumn to toColumn
                block += line.substring(fromColumn, toColumn);
            } else {
                // If the block spans multiple rows, take the substring from fromColumn to the end of the line
                block += line.substring(fromColumn);
            }
        } else if (i == toRow) {
            // For the last row, take the substring from the start of the line to toColumn
            block += line.substring(0, toColumn);
        } else {
            // For rows in between, take the whole line
            block += line;
        }

        // Add a newline character if it's not the last row
        if (i < toRow) {
            block += "\n";
        }
    }

    return block;
}


function get_text_from_syntaxnode(b: SyntaxNode, text: string): string {
	if (!b) {
		return "";
	}
	const fromRow = b.startRow;
	const toRow = b.endRow;
	const fromColumn = b.startColumn;
	const toColumn = b.endColumn;
	return get_text_block(fromRow, toRow, fromColumn, toColumn, text);
}



/*
	Mutates a Forge ``wheat'' (aka correct solution)
	to generate a mutant that is consistent with the student's
	tests.
*/
export class ConceptualMutator {
	skipped_tests: SkippedTest[];
	inconsistent_tests: string[];
	num_mutations = 0;

	wheat_util: ForgeUtil;
	student_util: ForgeUtil;
	full_source_util: ForgeUtil;

	mutant: HydratedPredicate[] = [];

	// ALSO HAVE TO THINK ABOUT THE FUNCTIONS.

	/**
	 * Creates a new Mutator instance.
	 * @param wheat - The 'wheat'
	 * @param student_tests - Tests authored by the student.
	 * @param forge_output - Forge output after the source_text was run in Forge.
	 * @param test_file_name - The name of the student test file.
	 * @param source_text - The source_text of the *actual* file that was run in Forge. In the case of a Toadus ponens run, this is what you get AFTER joining WHEAT + STUDENT_PREDICATES.
	 * @param max_mutations - The maximum number of mutations that can be carried out(default: 200).
	 */
	constructor(public wheat: string,
		public student_tests: string,
		public forge_output: string,
		public test_file_name: string,
		public source_text: string,
		public max_mutations: number = 200) {

		this.wheat_util = new ForgeUtil(wheat);
		//this.student_util = new ForgeUtil(student_tests);
		this.full_source_util = new ForgeUtil(source_text);

		this.wheat_util.processSpec();
		//this.student_util.processSpec();
		this.full_source_util.processSpec();
		this.inconsistent_tests = [];
		this.skipped_tests = [];





		// TODO: Maybe this should keep track of the passing and failing tests rather than the calling code.

		function predicateToHydratedPredicate(p: Predicate): HydratedPredicate {
			const name = p.name;
			const body_block: Block = p.body;


			const body = get_text_from_syntaxnode(body_block, source_text);
			let params_text = get_text_from_syntaxnode(p.params, source_text);

			// If the first character of params is '[' and the last character is ']',
			// we should remove the brackets.
			// This is hacky and I chalk it up to BAD parsing.
			if (params_text.startsWith("[") && params_text.endsWith("]")) {
				params_text = params_text.substring(1, params_text.length - 1);
			}


			const params = {};
			const param_strings = params_text.split(",");



			for (const param_string of param_strings) {
				const [name, type] = param_string.split(":");
				if (name && type) {
					params[name.trim()] = type.trim();
				}
			}
			return new HydratedPredicate(name, params, body);
		}

		this.mutant = this.full_source_util.getPreds().map(predicateToHydratedPredicate);
	}


	

	/**
	 * Mutate to remove belief.
	 * Modifies the mutant so that it fails passing tests of inclusion.
	 */
	public mutateToExcludeInclusionTests(): number {

		const assertions = this.full_source_util.getAssertions();
		const quantifiedAssertions = this.full_source_util.getQuantifiedAssertions();
		const examples = this.full_source_util.getExamples();
		const consistencyAssertions = this.full_source_util.getConsistencyAssertions();

		// TODO: Here we have to also think about the test expects. Deal with that later.

		for (const e of examples) {
			if (this.isTestOfInclusion(e)) {
				this.mutateAwayExample(e);
			}
		}

		for (const a of assertions) {
			if (this.isTestOfInclusion(a)) {

				// So the assertion is:
				// e implies p
				// So we want to exclude e from p.
				const pred = a.pred;
				const exp = get_text_from_syntaxnode(a.prop, this.source_text);
				this.constrainPredicateByExclusion(pred, exp);
			}
		}

		for (const qa of quantifiedAssertions) {
			if (this.isTestOfInclusion(qa)) {

				const pred = qa.pred;
				const exp = get_text_from_syntaxnode(qa.prop, this.source_text);
				const pred_args = this.getPredArgs(qa.predArgs);
				const quantifier = "all";
				const quantDecls = get_text_from_syntaxnode(qa.quantDecls, this.source_text);
				const disj = (qa.disj) ? "disj" : "";
				const quantifiedPrefix = `${quantifier} ${disj} ${quantDecls} | `;
				this.constrainPredicateByExclusion(pred, exp, quantifiedPrefix, pred_args);
			}
		}

		for (const ca of consistencyAssertions) {
			if (this.isTestOfInclusion(ca)) {

				const pred = ca.pred;
				const exp = get_text_from_syntaxnode(ca.prop, this.source_text);

				this.constrainPredicateByExclusion(pred, exp);
			}
		}

		return this.num_mutations;
	}


	/**
	 * Generates a mutant consistent with *all* tests of exclusion.
	 * @returns 
	 */
	public mutatefromExclusionTestIntersection(): number {

		// First mutate to vaccuity.
		this.mutateToVaccuity();

		const assertions = this.full_source_util.getAssertions();
		const quantifiedAssertions = this.full_source_util.getQuantifiedAssertions();
		const examples = this.full_source_util.getExamples();
		const consistencyAssertions = this.full_source_util.getConsistencyAssertions();

		// TODO: Here we have to also think about the test expects. Deal with that later.

		for (const e of examples) {
			if (this.isTestOfExclusion(e)) {
				// Ensure the mutant does not accept the example.
				this.mutateAwayExample(e);
			}
		}

		for (const a of assertions) {
			if (this.isTestOfExclusion(a)) {

				// THIS HAS TO CHANGE

				// Build the predicate under test from the assertion.
				const pred = a.pred;
				const exp = get_text_from_syntaxnode(a.prop, this.source_text);

				// If it is a test of exclusion, then we know it is
				// exp is necessary for <pred>
				// So we want to 
				this.constrainPredicateByInclusion(pred, exp);
			}
		}

		for (const qa of quantifiedAssertions) {
			if (this.isTestOfExclusion(qa)) {

				const pred = qa.pred;
				const exp = get_text_from_syntaxnode(qa.prop, this.source_text);
				const pred_args = this.getPredArgs(qa.predArgs);

				const quantifier = "all";
				const quantDecls = get_text_from_syntaxnode(qa.quantDecls, this.source_text);
				const disj = (qa.disj) ? "disj" : "";
				const quantifiedPrefix = `${quantifier} ${disj} ${quantDecls} | `;

				this.constrainPredicateByInclusion(pred, exp, quantifiedPrefix, pred_args);

			}
		}

		for (const ca of consistencyAssertions) {
			if (this.isTestOfExclusion(ca)) {
				// So we want to MUTATE TO the consistency assertion.
				const pred = ca.pred;
				const exp = get_text_from_syntaxnode(ca.prop, this.source_text);
				this.constrainPredicateByExclusion(pred, exp); // Exclude exp from pred.
			}
		}

		return this.num_mutations;
	}


	/**
	 * Modifies the mutant so that it passes failing tests.
	 * @returns The number of mutations carried out.
	 */
	public mutateToFailingTests(): number {

		const w_os = this.forge_output.split("\n");
		for (const w_o of w_os) {

			const testData = getFailingTestData(w_o);

			if (testData == undefined) {
				continue;
			}

			const testName = testData.name;
			const testType = testData.type;

			if (testType == "example") {
				const e = this.getExampleByName(testName);
				if (e == null) {
					this.skipped_tests.push(new SkippedTest(testName, `Could not find in source.`));
					continue;
				}
				this.mutateToExample(e);
			}
			else if (testType == "quantified_assertion") {
				const start_row = testData.startRow;
				const start_col = testData.startCol;

				const a = this.getQuantifiedAssertion(start_row, start_col);
				if (a == null) {
					this.skipped_tests.push(new SkippedTest(testName, `Could not find in source.`));
					continue;
				}
				this.mutateToQuantifiedAssertion(a);
			}
			else if (testType == "assertion") {

				const start_row = testData.startRow;
				const start_col = testData.startCol;
				const a = this.getAssertion(start_row, start_col);
				if (a == null) {
					this.skipped_tests.push(new SkippedTest(testName, `Could not find in source.`));
					continue;
				}
				this.mutateToAssertion(a);
			}
			else if (testType == "consistency_assertion") {
				const start_row = testData.startRow;
				const start_col = testData.startCol;
				const a = this.getConsistencyAssertion(start_row, start_col);
				if (a == null) {
					this.skipped_tests.push(new SkippedTest(testName, `Could not find in source.`));
					continue;
				}
				this.mutateToConsistencyAssertion(a);
			}
			else if (testType == "satisfiability_assertion") {
				this.skipped_tests.push(new SkippedTest(testName, `Cannot analyze sat/unsat assertions.`));
			}
			else if (testType == "test-expect") {
				this.skipped_tests.push(new SkippedTest(testName, `Cannot analyze test expects.`));
			}
			else if (testName != "") {
				this.skipped_tests.push(new SkippedTest(testName, `Unsupported test type.`));
			}
		}
		return this.num_mutations;
	}


	///////// TODO THE FUNTIONS ABOVE NEED TO BE REWRITTEN FOR THE NEW FORGE ////

	public getMutantAsString(): string {

		const predStrings = this.mutant.map((p) => {
			const declParams = p.declParams();
			const body = p.body;
			return `pred ${p.name}${declParams}\n {\n ${body} \n}`;
		});

		const PREFIX = "#lang forge\n option run_sterling off\n";
		const sigDecls = this.hydrateSigs();
		const sigs = sigDecls.join("\n\n");

		const functionDecls = this.hydrateFunctions();
		const fns = functionDecls.join("\n\n");

		const predicates = predStrings.join("\n\n");
		return `${PREFIX}\n${sigs}\n\n${fns}\n\n${predicates}`;

	}


	/**
	 * Not ideal. This is a low fidelity solution.
	 * @returns A list of sigs as strings.
	 */
	private hydrateSigs(): string[] {

		const sigs: Sig[] = this.full_source_util.getSigs();
		const sigStrings = sigs.map((s) => {
			const name = s.name;

			// I think this is the '' low fidelity '' solution for now.
			const body = get_text_from_syntaxnode(s, this.source_text);

			return body;
		});

		// I want to remove duplicates from the sigStrings.
		// TODO: THIS IS A HACK TO DEAL WITH SCENARIOS WHERE MULTIPLE SIGS ARE DEFINED IN THE SAME LINE

		const sigStringsSet = new Set(sigStrings);
		return Array.from(sigStringsSet);

	}

	/**
	 * Not ideal. This is a low fidelity solution.
	 * @returns A list of functions as strings.
	 */
	private hydrateFunctions(): string[] {
		const functions: Function[] = this.full_source_util.getFunctions();
		const functionStrings = functions.map((f) => {
			const name = f.name;
			const body = get_text_from_syntaxnode(f, this.source_text);
			return body;
		});

		return functionStrings;
	}


	private getExampleByName(name: string): Example {

		const examples = this.full_source_util.getExamples();
		for (const e of examples) {
			if (e.name == name) {
				return e;
			}
		}
		return null;
	}

	private getAssertion(start_row: number, start_col: number): AssertionTest {
		const assertions = this.full_source_util.getAssertions();
		for (const a of assertions) {
			// I think this is enough to uniquely identify the assertion.
			if (a.startRow == start_row && a.startColumn == start_col)
				return a;
		}
		return null;
	}


	private getQuantifiedAssertion(start_row: number, start_col: number): QuantifiedAssertionTest {
		const assertions: QuantifiedAssertionTest[] = this.full_source_util.getQuantifiedAssertions();
		for (const a of assertions) {

			// I think this is enough to uniquely identify the assertion.
			if (a.startRow == start_row && a.startColumn == start_col)
				return a;


		}
		return null;
	}

	private getConsistencyAssertion(start_row: number, start_col: number): ConsistencyAssertionTest {
		const assertions = this.full_source_util.getConsistencyAssertions();
		for (const a of assertions) {
			// I think this is enough to uniquely identify the assertion.
			if (a.startRow == start_row && a.startColumn == start_col)
				return a;
		}
		return null;
	}

	private getSatisfactionAssertion(start_row: number, start_col: number): SatisfiabilityAssertionTest {
		const assertions = this.full_source_util.getSatisfactionAssertions();
		for (const a of assertions) {
			// I think this is enough to uniquely identify the assertion.
			if (a.startRow == start_row && a.startColumn == start_col)
				return a;
		}
		return null;
	}


	private isInstructorAuthored(p: Predicate | string): boolean {

		// if p is a string, then it is the name of the predicate.
		// if p is a Predicate, then it is the predicate itself.
		let pname = (typeof p === "string") ? p : p.name;

		pname = pname.trim();

		const wheat_predicates: Predicate[] = this.wheat_util.getPreds();
		for (const wp of wheat_predicates) {
			if (wp.name == pname) {
				return true;
			}
		}
		return false;
	}


	private getNewName(name: string) {

		return `${name}_inner_${this.num_mutations}`;
	}

	///////// OPERATORS THAT EASE OR CONSTRAINT PREDICATES BY AN EXPRESSION ////////////////
	protected easePredicate(i: string, e: string, quantified_prefix = "", pred_args = ""): void {
		const p_i: HydratedPredicate = this.mutant.find((p) => p.name == i);

		if (!p_i) {
			throw new Error(`Predicate ${i} not found! Something is very wrong, please contact the instructor.`);
		}
		this.num_mutations++;
		const newName_i = this.getNewName(i);
		p_i.name = newName_i;
		const new_i_body = `${quantified_prefix} (${newName_i}${pred_args} or (${e}))`;

		const p_i_prime = new HydratedPredicate(i, p_i.params, new_i_body);
		this.mutant.push(p_i_prime);

	}


	protected constrainPredicateByInclusion(i: string, e: string, quantified_prefix = "", pred_args = ""): void {
		const p_i: HydratedPredicate = this.mutant.find((p) => p.name == i);
				this.num_mutations++;
		if (!p_i) {
			throw new Error(`Predicate ${i} not found! Something went wrong, please contact the instructor.`);
		}
		this.num_mutations++;
		const newName_i = this.getNewName(i);

		p_i.name = newName_i;
		const new_i_body = `${quantified_prefix} (${newName_i}${pred_args} and (${e}))`;
		const p_i_prime = new HydratedPredicate(i, p_i.params, new_i_body);
		this.mutant.push(p_i_prime);
	}

	protected constrainPredicateByExclusion(i: string, e: string, quantified_prefix = "", pred_args = ""): void {

		const p_i: HydratedPredicate = this.mutant.find((p) => p.name == i);

		if (!p_i) {
			throw new Error(`Predicate ${i} not found! Something is very wrong, please contact the instructor.`);
		}
		this.num_mutations++;
		const newName_i = this.getNewName(i);
		p_i.name = newName_i;

		const new_i_body = `${quantified_prefix} (${newName_i}${pred_args} and (not  (${e})))`;
		const p_i_prime = new HydratedPredicate(i, p_i.params, new_i_body);
		this.mutant.push(p_i_prime);
	}



	/////////////////// MUTATION OPERATIONS TO CONSISTENCY ////////////////////////////////

	protected mutateToAssertion(a: AssertionTest) {
		const pred = a.pred;
		const exp = get_text_from_syntaxnode(a.prop, this.source_text);
		const rel = a.check;

		const test_name = this.getTestName(a);
		if (!this.isInstructorAuthored(pred)) {
			this.skipped_tests.push(new SkippedTest(test_name, `Assertion does not directly test a predicate from the assignment statement.`));
			return;
		}

		this.inconsistent_tests.push(test_name);

		if (rel === "necessary") {
			this.constrainPredicateByInclusion(pred, exp);
		}
		else {
			this.easePredicate(pred, exp);
		}
	}

	protected mutateToQuantifiedAssertion(a: QuantifiedAssertionTest) {
		const pred = a.pred;
		const rel = a.check;
		const disj = (a.disj) ? "disj" : "";

		const test_name = this.getTestName(a);

		if (!this.isInstructorAuthored(pred)) {
			this.skipped_tests.push(new SkippedTest(test_name, `Assertion does not directly test a predicate from the assignment statement.`));
			return;
		}

		const exp = get_text_from_syntaxnode(a.prop, this.source_text);
		const pred_args = this.getPredArgs(a.predArgs); 
		const quantifier = "all";
		const quantDecls = get_text_from_syntaxnode(a.quantDecls, this.source_text);
		const quantifiedPrefix = `${quantifier} ${disj} ${quantDecls} | `;

		this.inconsistent_tests.push(test_name);
		if (rel === "necessary") {
			this.constrainPredicateByInclusion(pred, exp, quantifiedPrefix, pred_args);
		}
		else {
			this.easePredicate(pred, exp, quantifiedPrefix, pred_args);
		}
	}

	// TODO: Very much not sure how this works.
	protected mutateToExample(e: Example) {

		// TODO: We should get this from isTestOfInclusion / isTestOfExclusion


		// Determine if positive or negative example.
		// Find if testExpr
		const exampletestExpr = getExprFromBracesIfAny(get_text_from_syntaxnode(e.testExpr, this.source_text));
		const negativeExample = exampletestExpr.match(negationRegex);

		// Pred under test
		let p_i = exampletestExpr;
		if (negativeExample) {
			p_i = negativeExample[2];
		}

		// Ensure p_i is in the wheat.
		if (!this.isInstructorAuthored(p_i)) {
			this.skipped_tests.push(new SkippedTest(e.name, `Example does not directly test a predicate (or its negation) from the assignment statement.`));
			return;
		}

		this.inconsistent_tests.push(e.name);


		// Example to characteristic predicate.
		const hp = this.exampleToPredicate(e);

		this.mutant.push(hp);

		if (negativeExample) {
			// Student Belief: failedExample.exampleName => (not failedExample.examplePredicate)
			this.constrainPredicateByExclusion(p_i, hp.name);
		}
		else {
			// OR Student Belief :	failedExample.exampleName => failedExample.examplePredicate 
			this.easePredicate(p_i, hp.name);
		}
	}

	protected mutateToConsistencyAssertion(a: ConsistencyAssertionTest) {

		const pred = a.pred;
		const exp = get_text_from_syntaxnode(a.prop, this.source_text);
		const isConsistent: boolean = a.consistent;
		const consistency_prefix = isConsistent ? "consistent" : "inconsistent";

		const test_name = this.getTestName(a);
		if (!this.isInstructorAuthored(pred)) {
			this.skipped_tests.push(new SkippedTest(a.name, `Assertion does not directly test a predicate from the assignment statement.`));
			return;
		}

		this.inconsistent_tests.push(test_name);
		// If isconsistent, then they believe pred & exp is SAT.
		// SO WE need to EASE the predicate to ALLOW the expression.
		if (isConsistent) {
			this.easePredicate(pred, exp);
		}
		// If inconsistent, then they believe pred & exp is can never be SAT.
		// SO WE need to CONSTRAIN the predicate to EXCLUDE the expression.
		else {
			this.constrainPredicateByExclusion(pred, exp);
		}
	}

	private mutateToSatisfiabilityAssertion(a: SatisfiabilityAssertionTest) {
		/// How would this even work?
		throw new Error("Not implemented.");
	}


	private mutateToTest(t: Test) {
		throw new Error("Not implemented yet.");
	} // Not implemented yet, very HARD.

	public mutateToVaccuity() {
		this.mutant.forEach(
			(p) => {
				p.body = "";
			}
		);
	}


	////////////////// MUTATION OPERATIONS TO INCONSISTENCY /////////////////////////////////////
	// TODO: This is a very naive implementation. We should be able to do better.
	protected mutateAwayExample(e: Example) {

		// BUT ONLY IF THIS IS A POSITIVE EXAMPLE.

		const p = this.exampleToPredicate(e);
		this.mutant.push(p);

		// Now, we want to exclude this assertion from rhs.
		this.constrainPredicateByExclusion(e.name, p.name);
		// AND IF IT IS A NEGATIVE EXAMPLE? WE COULD EASE THE PREDICATE TO INCLUDE THE NEGATION OF THE EXAMPLE.

	}



	public get_skipped_tests_as_string(): string {
		const skipped_test_strings = this.skipped_tests.map((s) => {
			return `${s.test} : ${s.reason}`;
		});
		return skipped_test_strings.join("\n");
	}
	///////////////////////////////////////////////////////////////////////////////////


	// TODO: This needs to be really rewritten.
	// This is far too verbose, and is from the original Toadus.
	// As a result, this may not work with all example types.
	protected exampleToPredicate(e: Example): HydratedPredicate {

		const exampleName = e.name;
		const exampleBody = get_text_from_syntaxnode(e.bounds, this.source_text);

		// Now bounds have two components:
		// Assignments and expressions

		// We need to put ALL the assignments on sigs on the outside, and then expressions and relations inside.
		/*
			some disj ${atom_rhs_comma_sep} : ${atom_name} | {
				${atom_name} = ${atom_rhs}
					.... etc
				expressions
				relations
			}
		*/
		// TODO: ISSUE: What if the example has a some disj quantifier in its body? That would break this.


		function extractAssignments() {

			function assignmentContinued(x: string) {
				const t = x.replace(/\(/g, "").replace(/\)/g, "")
					.replace(/\{/g, "").replace(/\}/g, "").trim();
				return t.startsWith("`") || t.startsWith("->") || t.startsWith(",") || t.startsWith("+");
			}


			const lines = exampleBody.split('\n');
			const expressions: string[] = [];
			const assignments: Object[] = [];

			let currentAssignment = { variable: '', value: '' };
			let isAssignmentContinued = false;

			for (const l of lines) {
				const line = l.trim();
				if (line == '') {
					continue;
				}

				isAssignmentContinued = assignmentContinued(line);
				if (isAssignmentContinued) {
					currentAssignment.value += ' ' + line.trim();
				} else {
					assignments.push({ ...currentAssignment });
					if (/^\s*\w+\s*=/.test(line)) {
						const parts = line.split('=');
						const lhs = parts[0].trim();
						const rhs = parts[1].trim();
						currentAssignment = { variable: lhs, value: rhs };
						isAssignmentContinued = true;
					} else {
						expressions.push(line);
					}
				}
			}


			if (isAssignmentContinued) {
				assignments.push({ ...currentAssignment });
			}
			return [assignments, expressions];
		}




		const sigNames = this.full_source_util.getSigs().map((s: Sig) => s.name);

		function sigToExpr(assignment) {
			const atom_name = assignment.variable;
			const atom_rhs = assignment.value.replace(/`/g, '');
			const atom_rhs_list = atom_rhs
				.replace(/\s+|\n|\r/g, '') // Replace all whitespace, newline, or return with empty string
				.replace(/\+/g, ' ')
				.replace(/->/g, ' ')
				.split(' ').map(item => item.trim());

			// Remove any elements that are in sigNames
			const atom_rhs_set = new Set(atom_rhs_list.filter(item => !sigNames.includes(item)));
			// Remove any duplicates
			const atom_rhs_comma_sep = Array.from(atom_rhs_set).join(', ');

			let quantifier = "";
			let constraint = "";
			if (atom_rhs_comma_sep != '') {
				quantifier = sigNames.includes(atom_name) ? `some disj ${atom_rhs_comma_sep} : ${atom_name} | {\n` : '';
				constraint = `${atom_name} = ${atom_rhs}`;
			}

			return {
				quantifier,
				constraint
			};
		}


		const [assignments, expressions] = extractAssignments();

		// All the expressions go on the outside.
		const expressionString = expressions.join('\n');
		const sigExpressions = assignments.map(sigToExpr);
		const sigQuantifiers = sigExpressions.map(a => a.quantifier).filter(a => a != '');
		const sigQuantifiersAsString = sigQuantifiers.join("\n");
		const sigConstraints = sigExpressions.map(a => a.constraint).join("\n");
		const sigAssignmentsPostfix = '}'.repeat(sigQuantifiers.length) + "\n";

		const pred_body = `
		${sigQuantifiersAsString}
		${sigConstraints}
		${expressionString}
		${sigAssignmentsPostfix}
	`;

		return new HydratedPredicate(e.name, {}, pred_body);
	}



	private isTestOfInclusion(t: AssertionTest | Example | QuantifiedAssertionTest | ConsistencyAssertionTest): boolean {

		// If NOT instructor authored, then it is NOT a test of inclusion.
		if (isAssertionTest(t)) {
			const a = t as AssertionTest;
			const p = a.pred;
			const rel = a.check;
			return this.isInstructorAuthored(p) && (rel === "sufficient");
		} else if (isQuantifiedAssertionTest(t)) {
			const qa = t as QuantifiedAssertionTest;
			const p = qa.pred;
			const rel = qa.check;
			return this.isInstructorAuthored(p) && (rel === "sufficient");
		} else if (isExample(t)) {

			const e = t as Example;
			const exampletestExpr = getExprFromBracesIfAny(get_text_from_syntaxnode(e.testExpr, this.source_text));
			const negativeExample = exampletestExpr.match(negationRegex);

			// Pred under test
			let p_i = exampletestExpr;
			if (negativeExample) {
				p_i = negativeExample[2];
			}

			// Ensure p_i is in the wheat.
			if (!this.isInstructorAuthored(p_i)) {
				return false;
			}

			// If it is a positive example, then it is a test of inclusion.
			return !negativeExample;
		}
		else if (isConsistencyAssertionTest(t)) {

			const ca = t as ConsistencyAssertionTest;
			const p = ca.pred;
			const isConsistent = ca.consistent;
			return this.isInstructorAuthored(p) && isConsistent;
		}

		return false;
	}

	private isTestOfExclusion(t: AssertionTest | Example | QuantifiedAssertionTest | ConsistencyAssertionTest): boolean {

		if (isAssertionTest(t)) {
			const a = t as AssertionTest;
			const p = a.pred;
			const rel = a.check;

			return this.isInstructorAuthored(p) && (rel === "necessary");

		}
		else if (isQuantifiedAssertionTest(t)) {
			const qa = t as QuantifiedAssertionTest;
			const p = qa.pred;
			const rel = qa.check;
			return this.isInstructorAuthored(p) && (rel === "necessary");
		} else if (isExample(t)) {

			const e = t as Example;

			const exampletestExpr = getExprFromBracesIfAny(get_text_from_syntaxnode(e.testExpr, this.source_text));
			const negativeExample = exampletestExpr.match(negationRegex);

			// Pred under test
			let p_i = exampletestExpr;
			if (negativeExample) {
				p_i = negativeExample[2];
			}

			// Ensure p_i is in the wheat.
			if (this.isInstructorAuthored(p_i) && negativeExample) {
				return true;
			}
		}
		else if (isConsistencyAssertionTest(t)) {

			const ca = t as ConsistencyAssertionTest;
			const p = ca.pred;
			const isConsistent = ca.consistent;
			return this.isInstructorAuthored(p) && !isConsistent;
		}

		return false;
	}


	private testExprReferencesPredUnderTest(e: string, p: string): boolean {

		// Check if e contains p with word boundaries.
		const regex = new RegExp(`\\b${p}\\b`);
		return regex.test(e);



		return false;
	}

	
	private getPredArgs(predArgs : SyntaxNode | undefined) : string {
		if (!predArgs) {
			return "";
		}

		return '[' + get_text_from_syntaxnode(predArgs, this.source_text) + ']';
	}


	private getTestName(t: AssertionTest | Example | QuantifiedAssertionTest | ConsistencyAssertionTest): string {

		// The problem here is that
		// 1. We remove comments in the 'source_text' but not in the 'student_tests'
		// 2. The student test has stuff above the '//// Do not edit anything above this line ////' line.
		// As a result, we generate a version of the student tests as it would
		// appear in the source text, and then we can use that to get the row number.
		const winnowed_student_tests = combineTestsWithModel("", this.student_tests);
		
		
		// Check if winnowed_student_tests is a substring of this.student_tests
		let rowNumberOffset = 0;
		if (this.source_text.includes(winnowed_student_tests)) {
			const index = this.source_text.indexOf(winnowed_student_tests);
			const prefix = this.source_text.substring(0, index);
			rowNumberOffset = prefix.split('\n').length;

		}
		// I think this is still broken because of COMMENTS.

		function correctRowNumber(row: number) : number{
			let new_number = row - rowNumberOffset;
			if (new_number < 0) {
				new_number = 0;
			}
			return new_number;
		}

		if (isAssertionTest(t)) {
			const a = t as AssertionTest;
			const rel = a.check;
			const row = correctRowNumber(a.startRow);
			
			return `${rel}_assertion_for_${a.pred}[${row}:${a.startColumn}]`;
		}
		else if (isQuantifiedAssertionTest(t)) {
			const qa = t as QuantifiedAssertionTest;
			const row = correctRowNumber(qa.startRow);
			return `${qa.check}_quantified_assertion_for_${qa.pred}[${row}:${qa.startColumn}]`;
		} else if (isExample(t)) {
			const e = t as Example;
			return e.name;
		}
		else if (isConsistencyAssertionTest(t)) {
			const a = t as ConsistencyAssertionTest;
			const pred = a.pred;
			const exp = get_text_from_syntaxnode(a.prop, this.source_text);
			const isConsistent: boolean = a.consistent;
			const consistency_prefix = isConsistent ? "consistent" : "inconsistent";
			const row = correctRowNumber(a.startRow);
			return`${consistency_prefix}_assertion_for_${pred}[${row}:${a.startColumn}]`;

		}
		else if (isSatisfiabilityAssertionTest(t)) {
			const a = t as SatisfiabilityAssertionTest;
			const check = a.check;
			const row = correctRowNumber(a.startRow);
			return `${check}_assertion[${row}:${a.startColumn}]`;

		}
		else if (isTestExpect(t)) {
			const a = t as Test;
			return a.name;
		}

		return "unknown_test";
	}

}

