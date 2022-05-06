"use strict";

export function mapContinueImpl(init) {
    return (next) => (f) => (initialIndex) => {
        let result = init(initialIndex);
        while (true) {
            if (result.type === "yield") {
                result = next(result.value.qcj)(f(result.value.j));
            } else if (result.type === "return") {
                return result.value;
            } else {
                throw new Error("Failed pattern match.")
            }
        }
    };
}
