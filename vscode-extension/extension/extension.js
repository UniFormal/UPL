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

	vscode.workspace.onDidOpenTextDocument(function (d) {UPL.update(d)});
	vscode.workspace.onDidChangeTextDocument(function (e) {UPL.update(e.document)});
	
	// implementing the commands defined in package.json
	push(vscode.commands.registerCommand('upl.build', () => {
		vscode.window.showInformationMessage('UPL is active');
	}));
	// auto-completion
	push(vscode.languages.registerCompletionItemProvider('upl', {
		provideCompletionItems(doc, pos, canceltoken) {
			return UPL.complete(doc, pos);
		}
	}, '.'));
	// outline
	push(vscode.languages.registerDocumentSymbolProvider('upl', {
		provideDocumentSymbols(doc, canceltoken) {
			return UPL.symbols(doc);
		}
	}))
	// interaction with symbol under cursor
	push(vscode.languages.registerHoverProvider('upl', {
		provideHover(doc, pos, canceltoken) {
		  return UPL.hover(doc, pos)
		}
	}));
	push(vscode.languages.registerDefinitionProvider('upl', {
		provideDefinition(doc, pos, canceltoken) {
			return UPL.definitionLocation(doc,pos);
		}
	}))
	push(vscode.languages.registerSignatureHelpProvider('upl', {
		provideSignatureHelp(doc, pos, canceltoken, context) {
			return UPL.signatureHelp(doc,pos);
		}
	}, ['(']))
}

function deactivate() {}

module.exports = {
	activate,
	deactivate
}