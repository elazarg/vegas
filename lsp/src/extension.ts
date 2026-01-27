import * as vscode from 'vscode';
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  TransportKind
} from 'vscode-languageclient/node';

let client: LanguageClient;

export function activate(context: vscode.ExtensionContext) {
  // Resolve the JAR path relative to the extension root so packaging/debug both work
  const serverPath = context.asAbsolutePath('server/vegas.jar');

  const serverOptions: ServerOptions = {
    command: 'java',
    args: ['-cp', serverPath, 'vegas.lsp.ServerKt'],
    transport: TransportKind.stdio
  };

  const clientOptions: LanguageClientOptions = {
    documentSelector: [{ scheme: 'file', language: 'vegas' }],
    synchronize: {
      fileEvents: vscode.workspace.createFileSystemWatcher('**/*.vg'),
    },
  };

  client = new LanguageClient(
    'vegasLanguageServer',
    'Vegas Language Server',
    serverOptions,
    clientOptions
  );

  client.start();
}

export function deactivate(): Thenable<void> | undefined {
  if (!client) {
    return undefined;
  }
  return client.stop();
}
