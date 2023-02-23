package org.lbee.twophase;

import java.util.Map;

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