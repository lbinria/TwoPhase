package org.lbee.instrumentation.tla.variable;

import org.lbee.instrumentation.TraceProducerException;
import org.lbee.instrumentation.TrackableValue;
import org.lbee.instrumentation.TrackedVariable;
import org.lbee.instrumentation.TrackedVariableInfo;

@TrackedVariableInfo(name = "set_variable")
public class TLASetVariable<TValue extends TrackableValue> extends TrackedVariable {

    public void add(TValue value) throws TraceProducerException {
        this.apply("AddElement", value);
    }

    public void set(TrackableValue value) throws TraceProducerException {
        this.apply("Replace", value);
    }

}
