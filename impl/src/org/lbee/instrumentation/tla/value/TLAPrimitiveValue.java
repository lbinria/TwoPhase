package org.lbee.instrumentation.tla.value;

import org.lbee.instrumentation.TracedValueProperty;
import org.lbee.instrumentation.TrackedValue;

public abstract class TLAPrimitiveValue<T> extends TrackedValue {

    @TracedValueProperty(name="value")
    public T value;

    public TLAPrimitiveValue(T value) {
        this.value = value;
    }

}
