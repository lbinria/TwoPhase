package org.lbee.instrumentation.tla.value;

import org.lbee.instrumentation.TracedValue;
import org.lbee.instrumentation.TrackableValue;
import org.lbee.instrumentation.TrackedValue;

import java.util.Map;

@TracedValue(type = "record")
public class TLARecordValue extends TrackedValue {
    public TLARecordValue() {
        super();
    }

    public TLARecordValue(Map<String, TrackableValue> properties) {
        super(properties);
    }
}