package org.lbee.instrumentation.tla.variable;

import org.lbee.instrumentation.TraceProducerException;
import org.lbee.instrumentation.TrackedValue;
import org.lbee.instrumentation.TrackedVariable;

public class TLASetVariable<TValue extends TrackedValue> extends TrackedVariable {

    public void add(TValue value) throws TraceProducerException {
        this.apply("AddElement", value);
    }

    public void set(TrackedValue value) throws TraceProducerException {
        this.apply("Replace", value);
    }

}
