import * as path from 'path';
import * as vscode from 'vscode';
import { workspace, ExtensionContext, Diagnostic, DiagnosticSeverity, DiagnosticCollection, languages } from 'vscode';
import { HintGenerator } from './hintgenerator';
import { ensureForgeVersion } from './forge-utilities';

import { CnDProcess } from './cndprocess';



import {
	LanguageClient,
	LanguageClientOptions,
	ServerOptions,
	TransportKind
} from 'vscode-languageclient/node';

import { Logger, LogLevel, Event } from "./logger";
import { RacketProcess } from './racketprocess';

var os = require("os");
import { v4 as uuidv4 } from 'uuid';

let client: LanguageClient;

let forgeOutput = vscode.window.createOutputChannel('Forge Output');
let halpOutput = vscode.window.createOutputChannel('Toadus Ponens Output');


const forgeEvalDiagnostics = vscode.languages.createDiagnosticCollection('Forge Eval');


async function getUserId(context) {
	const UID_KEY = "FORGE_UID";

	try {
		var uid = await context.secrets.get(UID_KEY).toString();
	}
	catch {
		uid = uuidv4().toString();
		await context.secrets.store(UID_KEY, uid);
	}
	forgeOutput.appendLine(`Your anonymous ID is ${uid}.`);
	return uid;
}




function subscribeToDocumentChanges(context: vscode.ExtensionContext, myDiagnostics: vscode.DiagnosticCollection): void {

	context.subscriptions.push(
		vscode.workspace.onDidChangeTextDocument(e => myDiagnostics.delete(e.document.uri))
	);

	context.subscriptions.push(
		vscode.workspace.onDidCloseTextDocument(doc => myDiagnostics.delete(doc.uri))
	);
}

// TODO: Want to make this an extension method on TextDocument, but cannot wrangle it.
function textDocumentToLog(d, focusedDoc) {
	const content = d.getText();
	const filePath = d.isUntitled ? "untitled" : d.fileName;
	const fileName = path.parse(filePath).base;
	const fileExtension = path.extname(fileName);

	// Don't log files if they do not have '.frg' extension.
	if (fileExtension !== '.frg') {
		return {};
	}

	return {
		focused: focusedDoc,
		filename: fileName,
		fileContent: content
	};
}



export async function activate(context: ExtensionContext) {


	let currentSettings = vscode.workspace.getConfiguration('forge');
	let minSupportedVersion = String(currentSettings.get<string>('minVersion'));
	await ensureForgeVersion(minSupportedVersion, (s: string) => vscode.window.showErrorMessage(s));


	// inspired by: https://github.com/GrandChris/TerminalRelativePath/blob/main/src/extension.ts
	vscode.window.registerTerminalLinkProvider({
		provideTerminalLinks: (context, token) => {

			const matcher = RacketProcess.matchForgeError(context.line);
			if (!matcher) {
				return [];
			} else {
				const filename = matcher['fileName'];
				// verify that filename matches?
				const filePath = vscode.window.activeTextEditor?.document.uri.fsPath;
				const filePathFilename = filePath?.split(/[/\\]/).pop();
				// console.log(`${filePath}: active filename: ${filePathFilename}; filename: ${filename}`);
				if (filePathFilename !== filename) {
					// console.log("the line name is not the active filename");
					return [];
				}

				const line = matcher['linenum'];
				const col = matcher['colnum'];

				const tooltip = filePath + `:${line}:${col}`;
				return [
					{
						startIndex: matcher['index'],
						length: matcher['line'].length,
						tooltip: tooltip,
						filePath: filePath,
						line: line,
						column: col
					}
				];
			}
		},
		handleTerminalLink: (link: any) => {
			// const racket = RacketProcess.getInstance(forgeEvalDiagnostics, forgeOutput);
			// todo: need to double check if line could be undefined or null
			if (link.line !== undefined) {
				RacketProcess.showFileWithOpts(link.filePath, link.line, link.column);
			}
			else {
				RacketProcess.showFileWithOpts(link.filePath, null, null);
			}
		}
	});


	context.globalState.update('forge.isLoggingEnabled', true);
	vscode.commands.executeCommand('setContext', 'forge.isLoggingEnabled', true);

	const userid = await getUserId(context);
	var logger = new Logger(userid);


	let forgeDocs = vscode.commands.registerCommand('forge.openDocumentation', async () => {

		const DOCS_URL = 'https://csci1710.github.io/forge-documentation/home.html';
		vscode.env.openExternal(vscode.Uri.parse(DOCS_URL))
			.then((success) => {
				if (!success) {
					vscode.window.showErrorMessage(`Could not open Forge documentation from VS Code. It is available at ${DOCS_URL}`);
				}
			});
	});

	// Can this be an async function?
	// If so, what are the implications?
	const runFile = vscode.commands.registerCommand('forge.runFile', async () => {

		let isLoggingEnabled = context.globalState.get<boolean>('forge.isLoggingEnabled', false);
		const editor = vscode.window.activeTextEditor;


		if (!editor) {
			vscode.window.showErrorMessage(`No active text editor!`);
			return null;
		}

		const fileURI = editor?.document.uri;
		const filepath = fileURI?.fsPath;
		const runId = uuidv4();

		forgeOutput.clear();
		forgeOutput.show();

		// always auto-save before any run
		if (!editor?.document.save()) {
			console.error(`Could not save ${filepath}`);
			vscode.window.showErrorMessage(`Could not save ${filepath}`);
			return null;
		}

		// try to only run active forge file
		if (filepath.split(/\./).pop() !== 'frg') {
			vscode.window.showInformationMessage('Click on the Forge file first before hitting the run button :)');
			console.log(`cannot run file ${filepath}`);
			return;
		}


		let racket = RacketProcess.getInstance(forgeEvalDiagnostics, forgeOutput);
		let myStderr = '';

		forgeOutput.appendLine(`Running file "${filepath}" ...`);


		let stdoutListener = (data: string) => {
			const lst = data.toString().split(/[\n]/);
			for (let i = 0; i < lst.length; i++) {
				// this is a bit ugly but trying to avoid confusing students
				if (lst[i] === 'Sterling running. Hit enter to stop service.') {
					forgeOutput.appendLine('Sterling running. Hit "Continue" to stop service and continue execution.');
				} else {
					forgeOutput.appendLine(lst[i]);
				}
			}
		};


		let stderrListener = (data: string) => {
			myStderr += data;
		}

		let exitListener = (code: number) => {
			if (!racket.racketKilledManually) {
				if (myStderr != '') {
					racket.sendEvalErrors(myStderr, fileURI, forgeEvalDiagnostics);
				} else {
					RacketProcess.showFileWithOpts(filepath, null, null);
					racket.userFacingOutput.appendLine('Finished running.');
				}
			} else {
				RacketProcess.showFileWithOpts(filepath, null, null);
				racket.userFacingOutput.appendLine('Forge process terminated.');
			}


			// Output *may* have user file path in it. Do we want this?
			var payload = {
				"output-errors": myStderr,
				"runId": runId
			}
			logger.log_payload(payload, LogLevel.INFO, Event.FORGE_RUN_RESULT);
		}


		try {
			let p = racket.runFile(filepath, stdoutListener, stderrListener, exitListener);
			await p;

			if (isLoggingEnabled && editor) {

				const documentData = vscode.workspace.textDocuments.map((d) => {
					const focusedDoc = (d === editor.document);
					return textDocumentToLog(d, focusedDoc);
				}).filter((data) => Object.keys(data).length > 0);
	
	
				documentData['runId'] = runId;
	
				logger.log_payload(documentData, LogLevel.INFO, Event.FORGE_RUN);
			}
		}
		catch {
			const log = textDocumentToLog(editor.document, true);
			log['error'] = 'Could not run Forge process.';
			log['runId'] = runId;

			logger.log_payload(log, LogLevel.ERROR, Event.FORGE_RUN);
			vscode.window.showErrorMessage("Could not run Forge process.");
			console.error("Could not run Forge process.");
			return null;
		}
	});

	const stopRun = vscode.commands.registerCommand('forge.stopRun', () => {
		let racket = RacketProcess.getInstance(forgeEvalDiagnostics, forgeOutput);
		racket.kill(true);
	});

	const continueRun = vscode.commands.registerCommand('forge.continueRun', () => {
		let racket = RacketProcess.getInstance(forgeEvalDiagnostics, forgeOutput);
		if (!racket.continueEval()) {
			vscode.window.showErrorMessage('No active Forge process to continue.');
		}
	});


	const enableLogging = vscode.commands.registerCommand('forge.enableLogging', () => {
		context.globalState.update('forge.isLoggingEnabled', true);
		vscode.commands.executeCommand('setContext', 'forge.isLoggingEnabled', true);
	});

	const disableLogging = vscode.commands.registerCommand('forge.disableLogging', () => {
		context.globalState.update('forge.isLoggingEnabled', false);
		vscode.commands.executeCommand('setContext', 'forge.isLoggingEnabled', false);
	});


	const halp = vscode.commands.registerCommand('forge.halp', () => {
		halpOutput.clear();
		halpOutput.show();
		let isLoggingEnabled = context.globalState.get<boolean>('forge.isLoggingEnabled', false);



		if (!isLoggingEnabled) {
			halpOutput.appendLine('❗🐸❗ I can only be used if logging is enabled.');
			return;
		}




		const editor = vscode.window.activeTextEditor;

		if (!editor) {
			halpOutput.appendLine('❗🐸❗ No active editor. Please open a .frg file.');
			return;
		}
		const document = editor.document;
		const content = document.getText();
		const fileName = document.fileName;

		if (fileName.endsWith('.test.frg')) {
			var h = new HintGenerator(logger, halpOutput);
			h.generateHints(content, fileName)
				.then((result) => {

					try {
						var documentData = textDocumentToLog(document, true);
						documentData['halp_output'] = result;
						logger.log_payload(documentData, LogLevel.INFO, Event.HALP_RESULT);

						if (result.length > 0) {
							halpOutput.appendLine(result);
						}
					}
					finally {
						halpOutput.appendLine('🐸 Toadus Ponens run ended 🐸');
					}

				});
		} else {
			halpOutput.appendLine('❗🐸❗ I can only analyze test (.test.frg) files.');
		}
	});

	const killCnDProcessCommand = vscode.commands.registerCommand('forge.killCnDProcess', () => {
        CnDProcess.killInstanceIfExists();
        vscode.window.showInformationMessage('Cope and Drag process killed.');
    });


	// Check if the CnD server should be launched on activation
	const config = vscode.workspace.getConfiguration('forge');
	const launchCnD = config.get<boolean>('launchCnD', false);

	if (launchCnD) {
		const cndProcess = CnDProcess.getInstance();
	}

	context.subscriptions.push(runFile, stopRun, continueRun, enableLogging, disableLogging, halp, forgeEvalDiagnostics,
		forgeOutput, halpOutput, forgeDocs, killCnDProcessCommand);

	subscribeToDocumentChanges(context, forgeEvalDiagnostics);

	// The server is implemented in node
	const serverModule = context.asAbsolutePath(
		path.join('server', 'out', 'server.js')
	);
	// The debug options for the server
	// --inspect=6009: runs the server in Node's Inspector mode so VS Code can attach to the server for debugging
	const debugOptions = { execArgv: ['--nolazy', '--inspect=6009'] };

	// If the extension is launched in debug mode then the debug server options are used
	// Otherwise the run options are used
	const serverOptions: ServerOptions = {
		run: { module: serverModule, transport: TransportKind.ipc },
		debug: {
			module: serverModule,
			transport: TransportKind.ipc,
			options: debugOptions
		}
	};

	// Options to control the language client
	const clientOptions: LanguageClientOptions = {
		// Register the server for plain text documents
		documentSelector: [{ scheme: 'file', language: 'forge' }],
		synchronize: {
			// Notify the server about file changes to '.clientrc files contained in the workspace
			fileEvents: workspace.createFileSystemWatcher('**/.clientrc')
		}
	};

	// Create the language client and start the client.
	client = new LanguageClient(
		'forgeLanguageServer',
		'Forge Language Server',
		serverOptions,
		clientOptions
	);

	// Start the client. This will also launch the server
	client.start();
	console.log('Client and Server launched');
}

export function deactivate(): Thenable<void> | undefined {

	CnDProcess.killInstanceIfExists();

	let racket = RacketProcess.getInstance(forgeEvalDiagnostics, forgeOutput);
	// kill racket process
	racket.kill(false);
	if (!client) {
		return undefined;
	}

	return client.stop();
}
