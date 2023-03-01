package org.lbee.twophase;

import org.lbee.instrumentation.TracedValue;
import org.lbee.instrumentation.TracedValueProperty;
import org.lbee.instrumentation.TrackedValue;
import org.lbee.instrumentation.tla.TLARecordValue;
import org.lbee.instrumentation.tla.TLAStringValue;

@TracedValue(type="record")
public class TLAMsgs extends TLARecordValue {

    @TracedValueProperty(name="type")
    public TLAStringValue type;

    @TracedValueProperty(name="rm")
    public TLAStringValue rm;

    public TLAMsgs(TLAStringValue type, TLAStringValue rm) {
        this.type = type;
        this.rm = rm;
    }

    public TLAMsgs(TLAStringValue type) {
        this.type = type;
    }

}
