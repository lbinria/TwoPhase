package org.lbee.instrumentation.tla;

public class TLAStringVariable extends TLAVariable {

    public void set(TLAStringValue value) {
        this.apply("Replace", value);
    }

}
