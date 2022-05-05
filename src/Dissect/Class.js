"use strict";

export const mapContinueImpl = (next) => (f) => (initialResult) => {
    let result = initialResult;
    while (true) {
        if (result.type === "yield") {
            result = next(result.value.qcj)(f(result.value.j));
        } else if (result.type === "return") {
            return result.value;
        } else {
            throw new Error("Failed pattern match.")
        }
    }
}
