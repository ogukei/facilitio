
const { newZ3Engine, Z3Engine } = require('./z3.ts');
window.newZ3Engine = newZ3Engine;
window.Z3Engine = Z3Engine;

import('./pkg')
    .then(wasm => {
        
    })
    .catch(console.error);
