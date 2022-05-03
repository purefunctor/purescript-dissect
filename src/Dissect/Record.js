"use strict";

export function mapRecordF(f) {
    return (x) => {
        let { names, values, instances } = x;
        values = Object.fromEntries(Object.entries(values).map(
            ([key, value]) => {
                return [key, instances[key].map(f)(value)];
            }
        ));
        return { names, values, instances };
    };
}

export function bimapRecordF(f) {
    return (g) => (x) => {
        let { names, values, current, instances } = x;
        current = {
            name: current.name,
            value: instances[current.name].bimap(f)(g)(current.value),
        }
        return { names, values, current, instances };
    };
}

let loop = ({ names, values, instances, namesRest, valuesFinished }) => {
    while (namesRest.length) {
        let currentName = namesRest.shift();
        let currentValue = values[currentName];
        let { type, value } = instances[currentName].init(currentValue);
        if (type === "yield") {
            return {
                type: "yield",
                value: {
                    j: value.j,
                    qcj: {
                        names,
                        instances,
                        values,
                        currentName,
                        currentValue: value.qcj,
                        namesRest: namesRest,
                        valuesFinished,
                    }
                }
            }
        } else if (type === "return") {
            valuesFinished[currentName] = value;
        } else {
            throw new Error("Failed pattern match.");
        }
    }
    return {
        type: "return",
        value: {
            names,
            instances,
            values: valuesFinished,
        },
    };
};

export function initRecordF({ names, values, instances }) {
    return loop({ names, values, instances, namesRest: names.slice(), valuesFinished: {} });
}

export function nextRecordF(
    { names, values, instances, currentName, currentValue, namesRest, valuesFinished }
) {
    return (cork) => {
        let { type, value } = instances[currentName].next(currentValue)(cork);
        if (type === "yield") {
            return {
                type: "yield",
                value: {
                    j: value.j,
                    qcj: {
                        names,
                        values,
                        instances,
                        currentName,
                        currentValue: value.qcj,
                        namesRest,
                        valuesFinished,
                    }
                },
            };
        } else if (type === "return") {
            valuesFinished[currentName] = value;
            return loop({ names, values, instances, namesRest, valuesFinished });
        } else {
            throw new Error("Failed pattern match.")
        }
    };
}
