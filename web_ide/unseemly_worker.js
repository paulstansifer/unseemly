importScripts('wasm/libunseemly.js')

const { html__eval_program, generate__ace_rules, generate__ace_rules__for, wasm_init } = wasm_bindgen;

async function run() {
    await wasm_bindgen('./wasm/libunseemly_bg.wasm');

    // Doesn't seem to actually elucidate panics, though:
    wasm_init();

    self.addEventListener('message', function (msg) {
        var result = "[error]";
        try {
            if (msg.data.task == 'execute') {
                result = html__eval_program(msg.data.program, "unseemly");
            } else if (msg.data.task == 'ace_rules') {
                if (msg.data.program) {
                    result = generate__ace_rules__for(msg.data.program, msg.data.lang)
                } else {
                    result = generate__ace_rules(msg.data.lang)
                }
            }
        } finally {
            self.postMessage({ task: msg.data.task, output: result });
        }
    })
}

run();
