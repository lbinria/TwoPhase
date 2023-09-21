package org.lbee.protocol;

/**
 * Message
 */
public class Message {

    private final String from;
    private final String content;
    private final long senderClock;
    private final String to;

    public String getFrom() { return from; }
    public String getContent() { return content; }
    public String getTo() { return to; }
    public long getSenderClock() { return senderClock; }

    public Message(String from, String to, String content, long senderClock) {
        this.from = from;
        this.to = to;
        this.content = content;
        this.senderClock = senderClock;
    }

    /**
     * Create message from 4 strings (doesn't check length, so it can throw an out of bound exception)
     * @param components Strings used to construct the message
     */
    public Message(String[] components) {
        this.from = components[0];
        this.to = components[1];
        this.content = components[2];
        this.senderClock = Long.parseLong(components[3]);
    }

    @Override
    public String toString() {
        return String.join(";", new String[] { from, to, content, Long.toString(senderClock) });
    }
}
