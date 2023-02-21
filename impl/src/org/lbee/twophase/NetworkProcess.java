package org.lbee.twophase;

import java.io.*;
import java.net.Socket;

public abstract class NetworkProcess implements TLANamedProcess {

    private final Socket socket;
    private final InputStream inputStream;
    private final PrintWriter writer;

    protected final LogicalClock logicalClock;

    protected final TLALogger logger;

    private boolean shutdown;

    public boolean isShutdown() { return shutdown; }
    protected void shutdown() { shutdown = true; }

    public NetworkProcess(Socket socket) throws IOException {
        this.socket = socket;
        this.inputStream = socket.getInputStream();
        OutputStream outputStream = socket.getOutputStream();
        this.writer = new PrintWriter(outputStream, true);
        logicalClock = new LogicalClock();
        this.shutdown = false;
        logger = new TLALogger(this.getClock());
    }

    public LogicalClock getClock() {
        return this.logicalClock;
    }
    //abstract void run() throws IOException;

    protected void run() throws IOException {
        Message message = receive();

        if (message == null)
            return;

        System.out.printf("%s - %s receive message: `%s`...\n", this.logicalClock, this.getName(), message.getContent());
        // Sync process clock
        this.logicalClock.sync(message.getSenderClock());

        // Call receive with received message
        receive(message);
    }

    abstract void receive(Message message) throws IOException;

    protected Message receive() throws IOException {
        // Request for message destined to me
        writer.println("r:" + this.getName());
        BufferedReader reader = new BufferedReader(new InputStreamReader(this.inputStream));
        String data = reader.readLine();
        if (data.equals("null"))
            return null;
        else {
            String[] components = data.split(";");
            return new Message(components);
        }
    }

    protected boolean send(Message message) throws IOException {
        // Log event (hard-coded for now)
        //logger.log(this, "msgs", message.getContent());
        //logger.commit();
        // Send message to server
        writer.println("s:" + message.toString());
        // Read response
        BufferedReader reader = new BufferedReader(new InputStreamReader(this.inputStream));
        String data = reader.readLine();
        return !data.equals("null");
    }

    protected void sendRaw(String s) {
        writer.println(s);
    }

}
