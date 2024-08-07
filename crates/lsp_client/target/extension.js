"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.deactivate = exports.activate = void 0;
const vscode_1 = require("vscode");
const node_1 = require("vscode-languageclient/node");
let client;
async function activate(context) {
    const traceOutputChannel = vscode_1.window.createOutputChannel("MFL Language Server trace");
    const command = "mfl-lsp-server";
    const run = {
        command,
        options: {
            env: {
                ...process.env,
                RUST_LOG: "debug",
            }
        }
    };
    const serverOptions = {
        run,
        debug: run,
    };
    // If the extension is launched in debug mode then the debug server options are used.
    // Otherwise the run options are used.
    let clientOptions = {
        documentSelector: [{ scheme: "file", language: "mfl" }],
        synchronize: {},
        traceOutputChannel,
    };
    // Create the language client and start the client.
    client = new node_1.LanguageClient("mfl-language-server", "MFL Language Server", serverOptions, clientOptions);
    client.start();
}
exports.activate = activate;
function deactivate() {
    if (!client) {
        return undefined;
    }
    return client.stop();
}
exports.deactivate = deactivate;
//# sourceMappingURL=extension.js.map