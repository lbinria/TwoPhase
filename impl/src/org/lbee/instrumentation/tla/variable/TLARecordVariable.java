package org.lbee.instrumentation.tla.variable;

import org.lbee.instrumentation.TraceProducerException;
import org.lbee.instrumentation.TrackedValue;
import org.lbee.instrumentation.TrackedVariable;
import org.lbee.instrumentation.tla.value.TLAStringValue;

public class TLARecordVariable extends TrackedVariable {

    public <TValue extends TrackedValue> void set(String key, TValue value) throws TraceProducerException {
        this.apply("ExceptAt", new TLAStringValue(key), value);
    }

}

