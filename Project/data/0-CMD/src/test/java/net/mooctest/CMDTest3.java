package net.mooctest;

import static org.junit.Assert.*;

import org.junit.Test;

public class CMDTest3 {

	@Test
	public void testnnull() {
		CMD cmd = new CMD();
		CMD.Option.IntegerOption optionInt1 = new CMD.Option.IntegerOption('i', "test1");
		CMD.Option.IntegerOption optionInt2 = new CMD.Option.IntegerOption("test2");
		CMD.Option.LongOption optionLong1 = new CMD.Option.LongOption('l', "test3");
		CMD.Option.LongOption optionLong2 = new CMD.Option.LongOption("test4");
		CMD.Option.DoubleOption optionDouble1 = new CMD.Option.DoubleOption('d', "test5");
		CMD.Option.DoubleOption optionDouble2 = new CMD.Option.DoubleOption("test6");
		CMD.Option.StringOption optionString1 = new CMD.Option.StringOption('s', "test7");
		CMD.Option.StringOption optionString2 = new CMD.Option.StringOption("test8");
		CMD.Option.BooleanOption optionBoolean1 = new CMD.Option.BooleanOption('b', "test9");
		CMD.Option.BooleanOption optionBoolean2 = new CMD.Option.BooleanOption("test10");
		cmd.addOption(optionInt1);
		cmd.addOption(optionInt2);
		cmd.addBooleanOption(optionBoolean2.longForm());
		cmd.addBooleanOption(optionBoolean1.shortForm().charAt(0), optionBoolean1.longForm());
		cmd.addDoubleOption(optionDouble1.shortForm().charAt(0), optionDouble1.longForm());
		cmd.addDoubleOption(optionDouble2.longForm());
		cmd.addLongOption(optionLong1.shortForm().charAt(0), optionLong1.longForm());
		cmd.addLongOption( optionLong2.longForm());
		cmd.addStringOption(optionString2.longForm());
		cmd.addStringOption(optionString1.shortForm().charAt(0),optionString1.longForm());
		String[] arg1 = {"-i","null"};
		String[] arg2 = {"-l","null"};
		String[] arg3 = { "-d","null"};
		String[] arg4 = { "-s", ""};
		try {
			cmd.parse(arg1);
		} catch (CMD.OptionException e) {
			//e.printStackTrace();
			assertEquals( "Illegal value 'null' for option -i/--test1", e.getMessage());
		}
		try {
			cmd.parse(arg2);
		} catch (CMD.OptionException e) {
			//e.printStackTrace();
			assertEquals( "Illegal value 'null' for option -l/--test3", e.getMessage());
		}
		try {
			cmd.parse(arg3);
		} catch (CMD.OptionException e) {
			//e.printStackTrace();
			assertEquals( "Illegal value 'null' for option -d/--test5", e.getMessage());
		}
		try {
			cmd.parse(arg4);
		} catch (CMD.OptionException e) {
			//e.printStackTrace();
			assertEquals( "Illegal value 'null' for option -s/--test7", e.getMessage());
		}
	}
	

}

