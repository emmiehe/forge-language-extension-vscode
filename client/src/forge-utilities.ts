
import { spawn } from 'child_process';
import * as fs from 'fs';
import { tempFile } from './gen-utilities';

/*
	Utilites related to Forge syntax.
	Could change with Forge updates and/or a language server.
*/

export function removeForgeComments(inputText: string): string {
	let x = removeInlineComments(removeCStyleComments(inputText));
	// Normalize windows line endings
	x = x.replace(/\r/g, '');
	return x;
}

function removeCStyleComments(inputText: string): string {
	const regex = /\/\*[\s\S]*?\*\/|\/\/.*/g;
	return inputText.replace(regex, '');
}

function removeInlineComments(inputText: string): string {
	const regex = /--.*$/gm;
	return inputText.replace(regex, '');
}



export function findForgeExamples(inputText) {
	const withoutComments = removeForgeComments(inputText);
	const lines = withoutComments.split('\n');
	let inExample = false;
	let braceLevel = 0;
	let currentExample = '';
	let examples: string[] = [];

	for (let line of lines) {
		if (inExample) {
			currentExample += line + '\n';
			braceLevel += (line.match(/\{/g) || []).length;
			braceLevel -= (line.match(/\}/g) || []).length;

			if (braceLevel === 0) {
				examples.push(currentExample.trim());
				currentExample = '';
				inExample = false;
			}
		} else {
			// Adjusted regex to match the example syntax
			const match = line.match(/\bexample\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+is\s+(.*?)\s+for\s*\{/);
			if (match) {
				inExample = true;
				braceLevel = 1;
				currentExample = line + '\n';
			}
		}
	}

	return examples;
}


//// TODO: Can we fix these?

/****
 * Regex for extracting failing test names, types, and/or locations
 */
export const example_regex = 			  	/Invalid example '(\w+)'; the instance specified does not satisfy the given predicate\./;
const quantified_assertion_regex = 	/:(\d+):(\d+) \(span (\d+)\)\] Test quantified_(\w+)_assertion_for_(\w+)_([^\s\\]*) failed./;
const assertion_regex = 				/:(\d+):(\d+) \(span (\d+)\)\] Test (\w+)_assertion_for_(\w+)_([^\s\\]*) failed./;
const consistency_assertion_regex =  /:(\d+):(\d+) \(span (\d+)\)\] Failed test (consistent|inconsistent)_assertion_for_(\w+)_([^\s\\]*)/;
const satisfaction_assertion_regex = /:(\d+):(\d+) \(span (\d+)\)\] Failed test (sat|unsat|forge_error)_assertion_([^\s\\]*)/;
const test_regex = 					/Failed test (\w+)\.|Theorem (\w+) failed|Test (\w+) failed\./;

export class TestData {

	constructor(public name: string, public type: string, public startRow: number,
		public startCol: number, public span: number, public forgeOutput: string){ }
}

export function getFailingTestsData(o: string): TestData[] {
	let lines = o.split("\n");
	return lines.map(getFailingTestData).filter((x) => x != undefined);
}




// TODO: This needs to be RE-WRITTEN now that the test name is NOT obvious.
// TODO: Should we abstract out getting the test NAME, type, and location?
export function getFailingTestData(o: string): TestData {

	// TODO: Rewrite.
	// If a test HAS a name ...




	// Else if a test is IMPLICITLY named, ...




	if (quantified_assertion_regex.test(o)) {
		const match = o.match(quantified_assertion_regex);

		if (match == null) {
			return undefined;
		}

		let testName = match[4] + "_quantified_assertion_for_" + match[5] + "_" + match[6];
		return new TestData(testName,
							"quantified_assertion",
							 parseInt(match[1]),
							 parseInt(match[2]),
							 parseInt(match[3]), o);

		// Entire string is match[0]
		// Line number is match[1]
		// Column number is match[2]
		// Span is match[3]
		// Direction of assertion is match[4]
		// Predicate name is match[5]
		// Temp name is match[6]

	} else if (assertion_regex.test(o)) {
		const match = o.match(assertion_regex);
		if (match == null) {
			return undefined;
		}


		// Entire string is match[0]
		// Line number is match[1]
		// Column number is match[2]
		// Span is match[3]
		// Direction of assertion is match[4]
		// Predicate name is match[5]
		// Temp name is match[6]

		let test_name = match[4] + "_assertion_for_" + match[5] + "_" + match[6];
		return new TestData(test_name,
							"assertion",
							 parseInt(match[1]),
							 parseInt(match[2]),
							 parseInt(match[3]), o);

	} else if (example_regex.test(o)) {
		const match = o.match(example_regex);
		if (match == null) {
			return undefined;
		}
		
		let test_name = match[1];
		return new TestData(test_name,
							"example",
							 -1,
							 -1,
							 -1, o);
	}
	else if (consistency_assertion_regex.test(o)) {
		const match = o.match(consistency_assertion_regex);
		if (match == null) {
			return undefined;
		}
		let test_name = match[4] + "_assertion_for_" + match[5] + "_" + match[6];

		return new TestData(test_name,
							"consistency_assertion",
							 parseInt(match[1]),
							 parseInt(match[2]),
							 parseInt(match[3]), o);

	}
	else if (satisfaction_assertion_regex.test(o)) {
		const match = o.match(satisfaction_assertion_regex);
		if (match == null) {
			return undefined;
		}
		let test_name = match[4] + "_assertion_" + match[5];
		return new TestData(test_name,
							"satisfaction_assertion",
							 parseInt(match[1]),
							 parseInt(match[2]),
							 parseInt(match[3]), o);
	}
	else if (test_regex.test(o)) {
		const match = o.match(test_regex);
		if (match == null) {
			return undefined;
		}

		let test_name = (match[1]) ? match[1] : (match[2]) ? match[2] : match[3];

		return new TestData(test_name,
							"test-expect",
							 -1,
							 -1,
							 -1, o);
	}
	return undefined;
}

/*******For test suite  */

export type ExtractedTests = {

	examples: Object[];
	assertions: Object[];
	quantifiedAssertions: Object[];

};

export type ExtractedTestSuite = {
	predicateName: string;
	tests: ExtractedTests;
} | null;


function isBalancedBraces(content: string): boolean {
	const stack: string[] = [];
	for (const char of content) {
		if (char === '{') {
			stack.push(char);
		} else if (char === '}') {
			if (stack.length === 0) return false;
			stack.pop();
		}
	}
	return stack.length === 0;
}



///// Version Check //////////

function compareVersions(version1: string, version2: string): number {
	const parseVersion = (version: string) => version.split('.').map(Number);

	const v1 = parseVersion(version1);
	const v2 = parseVersion(version2);

	for (let i = 0; i < Math.max(v1.length, v2.length); i++) {
		// Treat missing parts as 0 (e.g., "1.0" is equal to "1.0.0")
		const num1 = i < v1.length ? v1[i] : 0;
		const num2 = i < v2.length ? v2[i] : 0;

		if (num1 > num2) return 1;
		if (num2 > num1) return -1;
	}

	return 0; // Versions are equal
}


export async function ensureForgeVersion(minVersion: string, error_reporter: (s: string) => void) {


	return ;

	const filePath = tempFile();
	const emptyForgeFile = `
	#lang forge
	option run_sterling off
	test expect {

		{} is sat
	}
	`;

	fs.writeFileSync(filePath, emptyForgeFile);
	let p = spawn('racket', [`"${filePath}"`], { shell: true });

	var stdout = '';
	var stderr = '';

	const ERR_FORGE = "Could not determine Forge version. Please ensure that Forge is installed.";
	p.stderr.on('data', (err: string) => {
		stderr += err;
	});

	p.stdout.on('data', (err: string) => {
		stdout += err;
	});

	await new Promise<void>((resolve, _) => {
		p.on('exit', (code: string) => {
			resolve();
		});
	});

	if (stderr != '') {
		error_reporter(stderr);
	} else if (stdout == '') {
		error_reporter(ERR_FORGE);
	} else {
		const forgeVersionRegex = /Forge version: (\d+\.\d+\.\d+)|(\d+.\d+)/;
		const match = stdout.match(forgeVersionRegex);
		if (match) {

			let version = (match[1] == undefined) ? (match[2] + ".0") : match[1];
			if (compareVersions(version, minVersion) < 0) {
				error_reporter(`You are running Forge version ${version}, which is too old for this extension. Please update to at least ${minVersion} for guaranteed compatibility.`);
			}
		} else {
			error_reporter(ERR_FORGE);
		}
	}
}

export function combineTestsWithModel(wheatText: string, tests: string): string {
	// If separator doesn't exist (in that case, look for #lang forge)
	const TEST_SEPARATOR = "//// Do not edit anything above this line ////"
	const hashlang_decl = "#lang";

	if (tests.includes(TEST_SEPARATOR)) {
		const startIndex = tests.indexOf(TEST_SEPARATOR) + TEST_SEPARATOR.length;
		tests = tests.substring(startIndex).trim();
	}

	tests = tests.replace(hashlang_decl, "// #lang");


	var combined = wheatText + "\n" + tests;
	combined = removeForgeComments(combined);

	combined = combined.replace(/\t/g, " ");
	combined = combined.replace(/\r/g, " ");

	return combined;
}
