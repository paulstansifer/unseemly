importScripts('libunseemly.js')

const { html__eval_program, generate__ace_rules, wasm_init } = wasm_bindgen;

async function run() {
    await wasm_bindgen('./libunseemly_bg.wasm');

    // Doesn't seem to actually elucidate panics, though:
    wasm_init();

    self.addEventListener('message', function (msg) {
        console.log("Got " + msg.data.task);
        var result = "[error]";
        try {
            if (msg.data.task == 'execute') {
                result = html__eval_program(msg.data.program, "unseemly");
            } else if (msg.data.task == 'ace_rules') {
                result = generate__ace_rules(msg.data.lang)
            }
        } finally {
            console.log("Returning " + result.length)
            self.postMessage({task: msg.task, output: result});
        }
    })

    // start off by getting the syntax highlighter once:
    self.postMessage({task: "ace_rules", output: generate__ace_rules("unseemly")});

}

run();
