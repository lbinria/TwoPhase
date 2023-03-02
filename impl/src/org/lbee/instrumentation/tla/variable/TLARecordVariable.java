package org.lbee.instrumentation.tla.variable;

import org.lbee.instrumentation.TraceProducerException;
import org.lbee.instrumentation.TrackableValue;
import org.lbee.instrumentation.TrackedVariable;
import org.lbee.instrumentation.TrackedVariableInfo;
import org.lbee.instrumentation.tla.value.TLARecordValue;
import org.lbee.instrumentation.tla.value.TLAStringValue;

import java.util.Map;

@TrackedVariableInfo(name = "record_variable")
public class TLARecordVariable extends TrackedVariable {

    public <TValue extends TrackableValue> void set(String key, TValue value) throws TraceProducerException {
        //this.set(new TLARecordValue(Map.of(key, value)));
        this.apply("ExceptAt", new TLAStringValue(key), value);
    }

    @Override
    public String toString() {
        return super.toString();
    }

}

