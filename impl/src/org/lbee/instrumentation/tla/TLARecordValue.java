package org.lbee.instrumentation.tla;

import org.lbee.instrumentation.TrackableValue;
import org.lbee.instrumentation.FormalValueType;

import java.util.Map;

@FormalValueType(type="record")
public class TLARecordValue implements TrackableValue<Map<String, TrackableValue<?>>> {

    private final Map<String, TrackableValue<?>> value;

    public TLARecordValue(Map<String, TrackableValue<?>> value) {
        this.value = value;
    }

    @Override
    public String toString() {
        return this.value.toString();
    }

    @Override
    public Map<String, TrackableValue<?>> getValue() {
        return this.value;
    }

    @Override
    public String getType() {
        return "record";
    }

}