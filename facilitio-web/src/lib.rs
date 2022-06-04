
use std::sync::{Arc};

use web_sys::{HtmlElement, HtmlTextAreaElement};

// @see https://rustwasm.github.io/wasm-bindgen/examples/wasm-in-wasm.html
use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use wasm_bindgen_futures::{spawn_local};
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

struct Z3Solver {
    z3: Z3Engine,
}

impl Z3Solver {
    async fn new() -> Arc<Self> {
        let z3 = newZ3Engine().await;
        let z3 = z3.dyn_into::<Z3Engine>().unwrap();
        let this = Self {
            z3,
        };
        Arc::new(this)
    }

    async fn eval(&self, input: &str) -> JsValue {
        let context = self.z3.mk_context();
        let result = self.z3.eval_smtlib2_string(&context, input).await;
        self.z3.del_context(&context);
        result
    }
}

fn set_in_progress(is_in_progress: bool) {
    let window = web_sys::window().unwrap();
    let document = window.document().unwrap();
    let in_progress = document
        .get_element_by_id("in-progress")
        .unwrap()
        .dyn_into::<HtmlElement>()
        .unwrap();
    in_progress.set_hidden(!is_in_progress);
}

fn fetch_input_text() -> String {
    let window = web_sys::window().unwrap();
    let document = window.document().unwrap();
    let input_element = document
        .get_element_by_id("input")
        .unwrap()
        .dyn_into::<HtmlTextAreaElement>()
        .unwrap();
    input_element.value()
}

fn set_output_text(text: &str) {
    let window = web_sys::window().unwrap();
    let document = window.document().unwrap();
    let output_element = document
        .get_element_by_id("output")
        .unwrap()
        .dyn_into::<HtmlTextAreaElement>()
        .unwrap();
    output_element.set_value(text);
}

fn set_enter_on_click_async<F>(f: F)
    where F: Fn() + 'static
{
    let window = web_sys::window().unwrap();
    let document = window.document().unwrap();
    let enter_button = document
        .get_element_by_id("enter")
        .unwrap()
        .dyn_into::<HtmlElement>()
        .unwrap();
    let closure = Closure::wrap(Box::new(f) as Box<dyn Fn()>);
    enter_button
        .set_onclick(Some(closure.as_ref().unchecked_ref()));
    closure.forget();
}

fn set_enter_enable(is_enabled: bool) {
    let window = web_sys::window().unwrap();
    let document = window.document().unwrap();
    let enter_button = document
        .get_element_by_id("enter")
        .unwrap()
        .dyn_into::<HtmlElement>()
        .unwrap();
    if is_enabled {
        enter_button.remove_attribute("disabled").unwrap();
    } else {
        enter_button.set_attribute("disabled", "disabled").unwrap();
    }
}

fn setup_ui(solver: &Arc<Z3Solver>) {
    set_in_progress(false);
    set_enter_enable(true);

    let closure_solver = Arc::clone(solver);
    set_enter_on_click_async(move || {
        let closure_solver = Arc::clone(&closure_solver);
        spawn_local(async move {
            console_log!("entered");
            set_enter_enable(false);
            set_in_progress(true);
            let input_text = fetch_input_text();
            console_log!("evaluating input {:?}", input_text);
            let output_text = closure_solver.eval(&input_text).await;
            console_log!("evaluation output {:?}", output_text);
            if let Some(text) = output_text.as_string() {
                set_output_text(&text);
            }
            set_in_progress(false);
            set_enter_enable(true);
        });
    });
}

async fn run_async() -> Result<(), JsValue> {
    console_log!("initializing Z3");
    let solver = Z3Solver::new().await;
    setup_ui(&solver);
    Ok(())
}

#[wasm_bindgen(start)]
pub fn run() {
    spawn_local(async {
        run_async().await.unwrap_throw();
    });
}
