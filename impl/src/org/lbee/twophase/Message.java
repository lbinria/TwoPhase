package org.lbee.twophase;

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
