
// @see https://github.com/Z3Prover/z3/blob/master/src/api/js/PUBLISHED_README.md
declare var initZ3: any;

import { init } from 'z3-solver/build/wrapper';

(async () => {
    let { em, Z3 } = await init(initZ3);
    let config = Z3.mk_config();
    let context = Z3.mk_context(config);
    let input = `
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
`;
    let output = await Z3.eval_smtlib2_string(context, input);
    console.log(output);
    Z3.del_context(context);
})();
