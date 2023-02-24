package org.lbee.instrumentation.tla;

import org.lbee.instrumentation.TrackedVariable;

import java.util.Map;

public class TLARecordVariable extends TrackedVariable<TLARecordValue> {

    @Override
    public void set(TLARecordValue recordValue) {

        this.apply("ExceptAt", recordValue);
    }

    public void set(String key, String value) {
        //
    }

    @Override
    public String toString() {
        return super.toString();
    }

}

