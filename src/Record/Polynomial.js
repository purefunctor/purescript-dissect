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
