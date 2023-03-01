package org.lbee.instrumentation.tla;

import org.lbee.instrumentation.TraceProducerException;
import org.lbee.instrumentation.TracedValueProperty;
import org.lbee.instrumentation.TrackedVariable;

public class TLAStringVariable extends TrackedVariable<TLAStringValue> {

    /**
     * @TraceUpdateMethod("set")
     * @param value
     */
    @Override
    public void set(TLAStringValue value) throws TraceProducerException {
        this.apply("Replace", value);
    }

}
