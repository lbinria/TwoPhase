package org.lbee.instrumentation.tla;

public class TLAStringVariable extends TLAVariable<TLAStringValue> {

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
