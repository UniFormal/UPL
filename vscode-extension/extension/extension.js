// this should be const, but making it global helps with debugging
vscode = require('vscode');
const upl = require('./src/main.js');

function activate(context) {
  console.log('Activating UPL');

  // subscribed disposables are automatically cleaned up when the extension is deactivated
  function push(disposable) { context.subscriptions.push(disposable); }

  const uplDiagnostics = vscode.languages.createDiagnosticCollection('upl');
  push(uplDiagnostics);

  // this should be const, but making it global helps with debugging
  UPL = new upl.VSCodeBridge(vscode, uplDiagnostics);

  vscode.workspace.onDidOpenTextDocument(function (d) { UPL.update(d) });
  vscode.workspace.onDidChangeTextDocument(function (e) { UPL.update(e.document) });


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
  }));
  // interaction with symbol under cursor
  push(vscode.languages.registerHoverProvider('upl', {
    provideHover(doc, pos, canceltoken) {
      return UPL.hover(doc, pos)
    }
  }));
  push(vscode.languages.registerDefinitionProvider('upl', {
    provideDefinition(doc, pos, canceltoken) {
      return UPL.definitionLocation(doc, pos);
    }
  }))
  push(vscode.languages.registerSignatureHelpProvider('upl', {
    provideSignatureHelp(doc, pos, canceltoken, context) {
      return UPL.signatureHelp(doc, pos);
    }
  }, ['(']))
  var encoder = new TextEncoder();
  var decoder = new TextDecoder();
  push(vscode.workspace.registerNotebookSerializer('upl-notebook', {
    deserializeNotebook: function (content, canceltoken) {
      var s = decoder.decode(content);
      let raw;
      try {
        raw = JSON.parse(s).cells;
      } catch {
        raw = [];
      }
      const cells = raw.map(
        item => new vscode.NotebookCellData(vscode.NotebookCellKind.code, item.source.join('\n'), item.cell_type)
      );
      return new vscode.NotebookData(cells);
    },
    serializeNotebook: function (data, canceltoken) {
      let contents = [];
      for (const cell of data.cells) {
        contents.push({
          cell_type: "code",
          source: cell.value.split(/\r?\n/g)

        });
      }
      return encoder.encode(JSON.stringify(contents))

    }
  }))
  function notebookExecuteHandler(cells, notebook, controller) {
    var ip = UPL.createInterpreter();
    cells.forEach(function(cell) {
      var execution = controller.createNotebookCellExecution(cell);
      execution.start(Date.now());
      var result = UPL.interpretExpression(ip, cell.index, cell.document.getText());
      var item = vscode.NotebookCellOutputItem.text(result);
      execution.replaceOutput([new vscode.NotebookCellOutput([item])]);
      execution.end(true, Date.now());
    })
  };
  var controller = vscode.notebooks.createNotebookController(
    "upl-controller", "upl-notebook", "UPL Notebook", notebookExecuteHandler);
  context.subscriptions.push(controller);
}

function deactivate() { }

module.exports = {
  activate,
  deactivate
}
