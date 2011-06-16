// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:18:40 PST by lamport  
//      modified on Thu May 31 13:24:56 PDT 2001 by yuanyu   

package tlc2.tool.distributed;

import java.io.IOException;
import java.net.InetAddress;
import java.rmi.ConnectException;
import java.rmi.Naming;
import java.rmi.RemoteException;
import java.rmi.server.UnicastRemoteObject;
import java.util.Date;

import tlc2.TLCGlobals;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateVec;
import tlc2.tool.WorkerException;
import tlc2.util.BitVector;
import tlc2.util.FP64;
import tlc2.util.LongVec;
import util.ToolIO;
import util.UniqueString;

/**
 * @version $Id$
 */
public class TLCWorker extends UnicastRemoteObject implements TLCWorkerRMI {

	private DistApp work;
	private FPSetManager fpSetManager;

	public TLCWorker(DistApp work, FPSetManager fpSetManager)
			throws RemoteException {
		this.work = work;
		this.fpSetManager = fpSetManager;
	}

	public synchronized Object[] getNextStates(TLCState[] states)
			throws WorkerException {
		TLCState state1 = null, state2 = null;
		int fpServerCnt = this.fpSetManager.numOfServers();
		TLCStateVec[] pvv = new TLCStateVec[fpServerCnt];
		TLCStateVec[] nvv = new TLCStateVec[fpServerCnt];
		LongVec[] fpvv = new LongVec[fpServerCnt];
		for (int i = 0; i < fpServerCnt; i++) {
			pvv[i] = new TLCStateVec();
			nvv[i] = new TLCStateVec();
			fpvv[i] = new LongVec();
		}
		try {
			// Compute all of the next states of this block of states.
			for (int i = 0; i < states.length; i++) {
				state1 = states[i];
				TLCState[] nstates = this.work.getNextStates(state1);
				for (int j = 0; j < nstates.length; j++) {
					long fp = nstates[j].fingerPrint();
					int fpIndex = (int) ((fp & 0x7FFFFFFFFFFFFFFFL) % fpServerCnt);
					pvv[fpIndex].addElement(state1);
					nvv[fpIndex].addElement(nstates[j]);
					fpvv[fpIndex].addElement(fp);
				}
			}

			BitVector[] visited = this.fpSetManager.containsBlock(fpvv);

			// Remove the states that have already been seen, check if the
			// remaining new states are valid and inModel.
			TLCStateVec[] newStates = new TLCStateVec[fpServerCnt];
			LongVec[] newFps = new LongVec[fpServerCnt];
			for (int i = 0; i < fpServerCnt; i++) {
				newStates[i] = new TLCStateVec();
				newFps[i] = new LongVec();
			}

			for (int i = 0; i < fpServerCnt; i++) {
				BitVector.Iter iter = new BitVector.Iter(visited[i]);
				int index;
				while ((index = iter.next()) != -1) {
					state1 = pvv[i].elementAt(index);
					state2 = nvv[i].elementAt(index);
					this.work.checkState(state1, state2);
					if (this.work.isInModel(state2)
							&& this.work.isInActions(state1, state2)) {
						state2.uid = state1.uid;
						newStates[i].addElement(state2);
						newFps[i].addElement(fpvv[i].elementAt(index));
					}
				}
			}
			// Prepare the return value.
			Object[] res = new Object[2];
			res[0] = newStates;
			res[1] = newFps;
			return res;
		} catch (WorkerException e) {
			throw e;
		} catch (Throwable e) {
			throw new WorkerException(e.getMessage(), state1, state2, true);
		}
	}

	public void exit() throws IOException {
		String hostname = InetAddress.getLocalHost().getHostName();
		ToolIO.out.println(hostname + ", work completed at: " + new Date()
				+ " Thank you!");
		
		UnicastRemoteObject.unexportObject(TLCWorker.this, true);
	}

	public static void main(String args[]) {
		ToolIO.out.println("TLC Worker " + TLCGlobals.versionOfTLC);

		// Must have exactly one arg: a hostname (spec is read from the server
		// connecting to).
		if(args.length != 1) {
			printErrorMsg("Error: Missing hostname of the TLC server to be contacted.");
			return;
		}
		final String serverName = args[0];

		String hostname = "Unknown";
		try {
			hostname = InetAddress.getLocalHost().getHostName();
			String url = "//" + serverName + ":" + TLCServer.Port
					+ "/TLCServer";
			
			// try to repeatedly connect to the server until it becomes available
			int sleep = 1000;
			TLCServerRMI server = null;
			while(true) {
				try {
					server = (TLCServerRMI) Naming.lookup(url);
					break;
				} catch (ConnectException e) {
					// if the cause if a java.NET.ConnectException the server is
					// simply not ready yet
					Throwable cause = e.getCause();
					if(cause instanceof java.net.ConnectException) {
						ToolIO.out.println("Server " + serverName
								+ " unreachable, sleeping " + sleep / 1000
								+ "s for server to come online...");
						Thread.sleep(sleep);
						sleep *= 2; // double wait time
					} else {
						// some other exception occurred which we cannot handle
						throw e;
					}
				}
			}

			long irredPoly = server.getIrredPolyForFP();
			FP64.Init(irredPoly);

			// this call has to be made before the first UniqueString gets
			// created! Otherwise workers and server end up creating different
			// unique strings for the same String value.
			UniqueString.setSource((InternRMI)server);

			DistApp work = new TLCApp(server.getSpecFileName(),
					server.getConfigFileName(), server.getCheckDeadlock(),
					server.getPreprocess(), new RMIFilenameToStreamResolver(
							server));

			FPSetManager fpSetManager = server.getFPSetManager();
			TLCWorkerRMI worker = new TLCWorker(work, fpSetManager);
			server.registerWorker(worker, hostname);

			ToolIO.out.println("TLC worker at " + hostname + " is ready at: "
					+ new Date());
		} catch (Throwable e) {
			// Assert.printStack(e);
			e.printStackTrace();
			ToolIO.out.println("Error: Failed to start worker at " + hostname
					+ " for server " + serverName + ".\n" + e.getMessage());
		}

		ToolIO.out.flush();
	}

	private static void printErrorMsg(String msg) {
		ToolIO.out.println(msg);
		ToolIO.out
				.println("Usage: java tlc2.tool.TLCWorker host");
	}

}
