package org.lbee.instrumentation.tla;

import org.lbee.instrumentation.TrackedVariable;

import java.util.Map;

public class TLARecordVariable extends TrackedVariable<TLARecordValue> {

    @Override
    public void set(TLARecordValue recordValue) {
        this.apply("Replace", recordValue);
    }

    public void set(String key, String value) {
        Map.Entry<?, ?> entry = Map.entry(key, value);
        this.apply("ExceptAt", entry);
    }

    @Override
    public String toString() {
        return super.toString();
    }

    @Override
    public String getType() { return "record"; }

}

