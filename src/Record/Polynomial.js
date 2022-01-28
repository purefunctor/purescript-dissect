"use strict";

exports.mapRecordF = (f) => (x) => {
    let { values, instances } = x;
    values = Object.fromEntries(Object.entries(values).map(
        ([key, value]) => {
            return [key, instances.functors[key].map(f)(value)];
        }
    ));
    return { values, instances };
};

exports.bimapRecordF = (f) => (g) => (x) => {
    let { done, todo, holed, instances } = x;
    holed = {
        key: holed.key,
        value: instances.bifunctors[holed.key].bimap(f)(g)(holed.value)
    };
    return { holed, instances, done, todo };
};

exports.unsafeLength = (record) => {
    return Object.keys(record).length;
};

exports.unsafeHead = (record) => {
    let entries = Object.entries(record);
    let [key, value] = entries.pop();
    return { key, value, rest: Object.fromEntries(entries) };
}
