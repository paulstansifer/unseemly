importScripts('wasm/libunseemly.js')

const { html__eval_program, generate__ace_rules, generate__ace_rules__for, stash_lang }
    = wasm_bindgen;

async function run() {
    await wasm_bindgen('./wasm/libunseemly_bg.wasm');

    self.addEventListener('message', function (msg) {
        var result = "[error]";
        try {
            if (msg.data.task == 'execute') {
                result = html__eval_program(msg.data.program, msg.data.lang);
            } else if (msg.data.task == 'stash') {
                stash_lang(msg.data.store_as, msg.data.program, msg.data.lang);
                result = '[done]';
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

    self.postMessage({ task: "startup" })
}

run();
