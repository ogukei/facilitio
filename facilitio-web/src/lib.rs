
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

#[wasm_bindgen]
extern "C" {
    type Z3Engine;

    #[wasm_bindgen(method)]
    fn mk_context(this: &Z3Engine) -> JsValue;

    #[wasm_bindgen(method)]
    fn del_context(this: &Z3Engine, context: &JsValue);

    #[wasm_bindgen(method)]
    async fn eval_smtlib2_string(this: &Z3Engine, context: &JsValue, input: &str) -> JsValue;
}

#[wasm_bindgen]
extern "C" {
    async fn newZ3Engine() -> JsValue;
}

macro_rules! console_log {
    ($($t:tt)*) => (log(&format_args!($($t)*).to_string()))
}

async fn run_async() -> Result<(), JsValue> {
    console_log!("initializing Z3");
    let z3 = newZ3Engine().await;
    let z3 = z3.dyn_into::<Z3Engine>().unwrap();
    let context = z3.mk_context();
    let input = "
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (>= (* 2 x) (+ y z)))
(declare-fun f (Int) Int)
(declare-fun g (Int Int) Int)
(assert (< (f x) (g x x)))
(assert (> (f y) (g x x)))
(check-sat)
(get-model)
(exit)
";
    let str = z3.eval_smtlib2_string(&context, input).await;
    console_log!("{:?}", str);
    z3.del_context(&context);
    Ok(())
}

#[wasm_bindgen(start)]
pub fn run() {
    spawn_local(async {
        run_async().await.unwrap_throw();
    });
}
