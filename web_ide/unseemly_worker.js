
importScripts('libunseemly.js')

const { html__eval_program, wasm_init } = wasm_bindgen;

async function run() {
    await wasm_bindgen('./libunseemly_bg.wasm');

    // Doesn't seem to actually elucidate panics, though:
    wasm_init();

    self.addEventListener('message', function (msg) {
        var result = "[error]";
        try {
            result = html__eval_program(msg.data);
        } finally {
            self.postMessage(result);
        }
    })
}

run();
