
// @see https://github.com/Z3Prover/z3/blob/master/src/api/js/PUBLISHED_README.md
declare var initZ3: any;

import { init } from 'z3-solver/build/wrapper';

export class Z3Engine {
    private Z3: any;

    constructor(em: any, Z3: any) {
        this.Z3 = Z3;
    }

    mk_context(): any {
        return this.Z3.mk_context(this.Z3.mk_config());
    }

    async eval_smtlib2_string(context: any, input: string): Promise<string> {
        return await this.Z3.eval_smtlib2_string(context, input);
    }

    del_context(context: any) {
        this.Z3.del_context(context);
    }
}

export async function newZ3Engine(): Promise<Z3Engine> {
    const { em, Z3 } = await init(initZ3);
    return new Z3Engine(em, Z3);
}
