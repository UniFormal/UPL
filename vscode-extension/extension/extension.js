// this should be const, but making it global helps with debugging
vscode = require('vscode');
const upl = require('./src/main.js');

function activate(context) {
	console.log('Activating UPL');

	// subscribed disposables are automatically cleaned up when the extension is deactivated
	function push(disposable) {context.subscriptions.push(disposable);}

	const uplDiagnostics = vscode.languages.createDiagnosticCollection('upl')
	push(uplDiagnostics);

    // this should be const, but making it global helps with debugging
	UPL = new upl.VSCodeBridge(vscode, uplDiagnostics);

	function update(event) {
		// console.log("update " + event.document.fileName);
		UPL.update(event.document);
	}
	vscode.workspace.onDidOpenTextDocument(update);
	vscode.workspace.onDidChangeTextDocument(update);
	
	// implementing the commands defined in package.json
	push(vscode.commands.registerCommand('upl.build', () => {
		vscode.window.showInformationMessage('UPL is active');
	}));
	// hovering
	push(vscode.languages.registerHoverProvider('upl', {
		provideHover(doc, pos, canceltoken) {
		  return UPL.hover(doc, pos)
		}
	}));
	// auto-completion
	push(vscode.languages.registerCompletionItemProvider('upl', {
		provideCompletionItems(document, position, canceltoken) {
			return [new vscode.CompletionItem("complete")];
		}
	}, '.', '\"'))
	// outline
	// registerDocumentSymbolProvider
}


function deactivate() {}

module.exports = {
	activate,
	deactivate
}