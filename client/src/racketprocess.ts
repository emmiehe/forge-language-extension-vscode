import { ChildProcess, spawn, execSync } from 'child_process';
import * as os from 'os';
import * as vscode from 'vscode';
import { Diagnostic, DiagnosticCollection, DiagnosticSeverity } from 'vscode';


export class RacketProcess {


	private static instance: RacketProcess | null = null; // Singleton instance
    private childProcess: ChildProcess | null;
    public racketKilledManually: boolean;
    public userFacingOutput: vscode.OutputChannel;
    private evalDiagnostics: vscode.DiagnosticCollection;



	constructor(evalDiagnostics: vscode.DiagnosticCollection, userFacingOutput: vscode.OutputChannel) {
		this.evalDiagnostics = evalDiagnostics;
		this.userFacingOutput = userFacingOutput;
		this.childProcess = null;
		this.racketKilledManually = false;
	}

	// Singleton pattern to ensure only one instance
	public static getInstance(evalDiagnostics: vscode.DiagnosticCollection, userFacingOutput: vscode.OutputChannel): RacketProcess {
		if (!RacketProcess.instance) {
			RacketProcess.instance = new RacketProcess(evalDiagnostics, userFacingOutput);
		}
		return RacketProcess.instance;
	}


	
	runFile(filePath: string,
			stdoutListener?: (data: string) => void,
			stderrListener? : (data: string) => void,
			exitListener? : (code: number) => void) : Promise<void>
	{

		return new Promise<void>((resolve, reject) => {
            // Always auto-save before any run
            if (!vscode.window.activeTextEditor?.document.save()) {
                console.error(`Could not save ${filePath}`);
                vscode.window.showErrorMessage(`Forge run failed. Could not save ${filePath}`);
                reject(new Error(`Could not save ${filePath}`));
                return;
            }

            this.kill(false);
            this.racketKilledManually = false;

            this.childProcess = spawn('racket', [`"${filePath}"`], { shell: true });

            this.childProcess.stdout?.on('data', (data) => {
                if (stdoutListener) {
                    stdoutListener(data.toString());
                }
            });

            this.childProcess.stderr?.on('data', (data) => {
                if (stderrListener) {
                    stderrListener(data.toString());
                }
            });

            this.childProcess.on('exit', (code) => {
				if (exitListener) {
					exitListener(code);
				}
				else if (code !== 0 && code !== 1) {
					// I *think* this is because Racket exits with code 1 when there is a
					// test failure.
						vscode.window.showErrorMessage(`Racket process exited with code ${code}`);
						reject(new Error(`Racket process exited with code ${code}`));
				}

				resolve();
                this.cleanup();
            });
        });
	}


	continueEval() {
		if (this.childProcess) {
			return this.childProcess.stdin?.write('\n');
		}
		return false;
	}

	destroy() {
		if (this.childProcess) {
			this.childProcess.kill();
			this.childProcess = null;
		}
	}


	kill(manual: boolean) {


		if (this.childProcess) {
			this.racketKilledManually = manual;
			const oldPid = this.childProcess.pid;
            console.log(`Killing Racket process, PID: ${oldPid}.`);
            const platform = os.platform();

            if (platform === 'win32') {
                // Use taskkill on Windows
                try {
                    execSync(`taskkill /PID ${oldPid} /T /F`, { stdio: 'inherit' });
                    console.log('Racket process killed successfully on Windows');
					this.userFacingOutput.appendLine('Racket process killed successfully on Windows');
                } catch (error) {
                    console.error(`Failed to kill Racket process on Windows:`, error);
					this.userFacingOutput.appendLine(`Failed to kill Racket process: ${error}`);
                }
            } else {
                // Use SIGTERM on Unix-like systems
                try {
                    this.childProcess.kill('SIGTERM');
                    console.log('Sent SIGTERM to Racket process, waiting for it to terminate...');
					
                    // Wait for a few seconds and then forcefully kill if still running
                    setTimeout(() => {
						console.log(`SIGKILL: Old PID: ${oldPid}), new PID ${this.childProcess.pid}`);
						
                        if (this.childProcess && !this.childProcess.killed) {
                            console.log('Racket process did not terminate, sending SIGKILL...');
                            this.childProcess.kill('SIGKILL');
                        }
                    }, 5000); // Wait for 5 seconds before sending SIGKILL
                } catch (error) {
                    console.error(`Failed to kill Racket process:`, error);
					this.userFacingOutput.appendLine(`Failed to kill Racket process: ${error}`);
                }
            }
			this.cleanup();
            this.childProcess = null;
		}
	}

    private cleanup(): void {
        if (this.childProcess) {
            this.childProcess.removeAllListeners();
            this.childProcess = null;
        }
    }

		
	sendEvalErrors(text: string, fileURI: vscode.Uri, diagnosticCollectionForgeEval: DiagnosticCollection) {


		function errLocationToDiagnostic(errLocation: any): Diagnostic {

			return {
				severity: DiagnosticSeverity.Error,
				range: errLocation['range'],
				message: `Forge Evaluation Error: ${errLocation['line']}`,
				source: 'Racket'
			};
		}

		this.userFacingOutput.appendLine(text);

		const textLines = text.split(/[\n\r]/);

		const errorList = textLines.map((line) => RacketProcess.matchForgeError(line)).filter((x) => x != null);
		const diagnostics: Diagnostic[] = errorList.map(errLocationToDiagnostic);

		diagnosticCollectionForgeEval.set(fileURI, diagnostics);


		const linenum = errorList.length > 0 ? errorList[0]['linenum'] : null;
		const colnum = errorList.length > 0 ? errorList[0]['colnum'] : null;
		RacketProcess.showFileWithOpts(fileURI.fsPath, linenum, colnum);
	}


	// TODO: Do these have to change?
	static matchForgeError(line: string): Object | null {

		/* There are multiple types of errors that can be thrown by Forge.*/
		const testFailurePattern = /[\\/]*?([^\\/\n\s]*\.frg):(\d+):(\d+) \(span (\d+)\)\]/;
		const raiseSyntaxErrorPattern = /[\\/]*?([^\\/\n\s]*\.frg):(\d+):(\d+):?/;  // assumes no space in filename
		const raiseForgeErrorWithFileNamePattern = /#<path:(.*?)> \[line=(\d+), column=(\d+), offset=(\d+)\]/;
		const raiseForgeErrorPattern = /.*\[line=(\d+), column=(\d+), offset=(\d+)\]/;
		const generalLocPattern = /at loc: line (\d+), col (\d+), span: (\d+)/;
		const generalsrcLocPattern = /.*\(srcloc #<path:(.*?)> (\d+) (\d+) (\d+) (\d+)\)/;

		const raiseSyntaxErrorMatch = line.match(raiseSyntaxErrorPattern);
		const raiseForgeErrorWithFileNameMatch = line.match(raiseForgeErrorWithFileNamePattern);
		const raiseForgeErrorMatch = line.match(raiseForgeErrorPattern);
		const generalLocMatch = line.match(generalLocPattern);
		const generalsrcLocMatch = line.match(generalsrcLocPattern);

		const generalTestFailureMatch = line.match(testFailurePattern);



		let linenum, colnum, index;
		let span = -1;
		let filename = vscode.window.activeTextEditor?.document.fileName || ''; // Default to current file
		if (generalTestFailureMatch) {
			filename = generalTestFailureMatch[1];
			linenum = parseInt(generalTestFailureMatch[2]) - 1;
			colnum = parseInt(generalTestFailureMatch[3]) - 1;
			span = parseInt(generalTestFailureMatch[4]);
			index = generalTestFailureMatch.index;
		}
		else if (raiseSyntaxErrorMatch) {
			filename = raiseSyntaxErrorMatch[1];
			linenum = parseInt(raiseSyntaxErrorMatch[2]) - 1;
			colnum = parseInt(raiseSyntaxErrorMatch[3]) - 1;
			index = raiseSyntaxErrorMatch.index;
		}
		else if (raiseForgeErrorWithFileNameMatch) {
			filename = raiseForgeErrorWithFileNameMatch[1];
			linenum = parseInt(raiseForgeErrorWithFileNameMatch[2]) - 1;
			colnum = parseInt(raiseForgeErrorWithFileNameMatch[3]) - 1;
			index = raiseForgeErrorWithFileNameMatch.index;
		}
		else if (raiseForgeErrorMatch) {

			linenum = parseInt(raiseForgeErrorMatch[1]) - 1;
			colnum = parseInt(raiseForgeErrorMatch[2]) - 1;
			index = raiseForgeErrorMatch.index;

		}
		else if (generalsrcLocMatch) {
			filename = generalsrcLocMatch[1];
			linenum = parseInt(generalsrcLocMatch[2]) - 1;
			colnum = parseInt(generalsrcLocMatch[3]) - 1;
			span = parseInt(generalsrcLocMatch[5]) - 1;
			index = generalsrcLocMatch.index;
		}

		else if (generalLocMatch) {
			linenum = parseInt(generalLocMatch[1]) - 1;
			colnum = parseInt(generalLocMatch[2]) - 1;
			span = parseInt(generalLocMatch[3]) - 1;
			index = generalLocMatch.index;
		}
		else {
			return null;
		}

		linenum = Math.max(0, linenum);
		colnum = Math.max(0, colnum);
		span = Math.max(1, span);

		const start = new vscode.Position(linenum, colnum);
		const end = new vscode.Position(linenum, colnum + span);
		const range = new vscode.Range(start, end);

		return { linenum, colnum, start, end, range, line, index, filename };
	}

	// This does not support multiple lines
	static showFileWithOpts(filePath: string, line: number | null, column: number | null) {
		if (line === null || column === null) {
			vscode.commands.executeCommand('vscode.open', vscode.Uri.file(filePath));
		} else {
			const start = new vscode.Position(line, column);
			const end = new vscode.Position(line, column);
			const range = new vscode.Range(start, end);

			const opts: vscode.TextDocumentShowOptions = {
				selection: range
			};

			vscode.commands.executeCommand('vscode.open', vscode.Uri.file(filePath), opts);
		}
	}
}


