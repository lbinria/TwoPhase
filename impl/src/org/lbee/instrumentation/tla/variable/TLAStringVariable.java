package org.lbee.instrumentation.tla.variable;

import org.lbee.instrumentation.TraceProducerException;
import org.lbee.instrumentation.TrackedVariable;
import org.lbee.instrumentation.tla.value.TLAStringValue;

public class TLAStringVariable extends TrackedVariable {

    public void set(TLAStringValue value) throws TraceProducerException {
        this.apply("Replace", value);
    }

}
