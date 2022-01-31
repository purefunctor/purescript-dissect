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
