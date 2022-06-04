
// @see https://rustwasm.github.io/wasm-bindgen/examples/wasm-in-wasm.html
use js_sys::{Function, Object, Reflect, WebAssembly};
use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use wasm_bindgen_futures::{spawn_local, JsFuture};
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = console)]
    fn log(a: &str);
}

macro_rules! console_log {
    ($($t:tt)*) => (log(&format_args!($($t)*).to_string()))
}

async fn run_async() -> Result<(), JsValue> {
    console_log!("instantiating a new wasm module directly");
    Ok(())
}

#[wasm_bindgen(start)]
pub fn run() {
    spawn_local(async {
        run_async().await.unwrap_throw();
    });
}
