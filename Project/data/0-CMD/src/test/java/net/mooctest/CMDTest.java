package net.mooctest;

import static org.junit.Assert.*;

import org.junit.Test;

public class CMDTest {

	@Test
	public void test() {
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
		String[] arg1 = {"-i","10", "-l","10", "-d","10.0", "-s", "abc", "-b", "true"};
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
		try {
			cmd.parse(arg1);
			assertEquals(10, (long) cmd.getOptionValue(optionInt1));
			assertEquals("true", cmd.getRemainingArgs()[0]);
		} catch (CMD.OptionException e) {
			e.printStackTrace();
		}
	}

	@Test
	public void test2() {
		CMD cmd = new CMD();
		CMD.Option.IntegerOption optionInt1 = new CMD.Option.IntegerOption('i', "test1");
		CMD.Option.IntegerOption optionInt2 = new CMD.Option.IntegerOption("test2");
		String[] arg1 = {"-i","10", "-l","10", "-d","10.0", "-s", "abc", "-b", "true"};
		cmd.addIntegerOption(optionInt2.longForm());
		cmd.addIntegerOption(optionInt1.shortForm().charAt(0),optionInt1.longForm());
		try {
			cmd.parse(arg1);
		}catch (CMD.UnknownOptionException c ){
			assertEquals("Unknown option '-l'", c.getMessage());
			assertEquals("-l", c.getOptionName());
		}
		catch (CMD.OptionException e) {
			//e.printStackTrace();
		}
	}
}

