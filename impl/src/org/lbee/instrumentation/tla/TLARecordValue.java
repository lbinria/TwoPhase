package org.lbee.instrumentation.tla;

import org.lbee.instrumentation.FormalValue;
import org.lbee.instrumentation.FormalValueType;

import java.util.Map;

@FormalValueType(type="record")
public class TLARecordValue implements FormalValue<Map<String, FormalValue<?>>> {

    private final Map<String, FormalValue<?>> value;

    public TLARecordValue(Map<String, FormalValue<?>> value) {
        this.value = value;
    }

    @Override
    public String toString() {
        return this.value.toString();
    }

    @Override
    public Map<String, FormalValue<?>> getValue() {
        return this.value;
    }

}