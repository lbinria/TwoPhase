package org.lbee.instrumentation.tla;

import org.lbee.instrumentation.TrackableValue;
import org.lbee.instrumentation.FormalValueType;
import org.lbee.instrumentation.TrackedValue;

import java.util.Map;
import java.util.stream.Collectors;

public class TLARecordValue extends TrackedValue<Map<String, TrackableValue<?>>> {

    public TLARecordValue(Map<String, TrackableValue<?>> value) {
        super(value, "record");
    }

    @Override
    public String toString() {
        String strValue = this.getValue().entrySet().stream().map(e -> "{\"" + e.getKey() + "\":" + e.getValue().toString() + "}").collect(Collectors.joining(","));
        return "{\"type\":\"" + this.getType() + "\",\"value\":" + strValue + "}";
    }
}