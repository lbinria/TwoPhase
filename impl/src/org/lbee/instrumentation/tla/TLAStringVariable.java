package org.lbee.instrumentation.tla;

import org.lbee.instrumentation.TrackedVariable;

public class TLAStringVariable extends TrackedVariable<TLAStringValue> {

    /**
     * @TraceUpdateMethod("set")
     * @param value
     */
    @Override
    public void set(TLAStringValue value) {
        this.apply("Replace", value);
    }

    @Override
    public String getType() { return "string"; }
}
