package org.lbee.instrumentation.tla.variable;

import org.lbee.instrumentation.TraceProducerException;
import org.lbee.instrumentation.TrackedValue;
import org.lbee.instrumentation.TrackedVariable;
import org.lbee.instrumentation.tla.value.TLABoolValue;

public class TLABoolVariable extends TrackedVariable {

    public <TValue extends TrackedValue> void set(boolean value) throws TraceProducerException {
        this.apply("Replace", new TLABoolValue(value));
    }

}
