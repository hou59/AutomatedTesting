package net.mooctest;

import static org.junit.Assert.*;

import org.junit.Test;

public class CMDTest2 {

	@Test
	public void test5() {
		CMD cmd = new CMD();
		CMD.Option.IntegerOption optionInt1 = new CMD.Option.IntegerOption('i', "test1");
		CMD.Option.IntegerOption optionInt2 = new CMD.Option.IntegerOption("test2");
		CMD.Option.LongOption optionLong1 = new CMD.Option.LongOption('l', "test3");
		String[] arg1 = {"-i-l"};
		cmd.addIntegerOption(optionInt2.longForm());
		cmd.addIntegerOption(optionInt1.shortForm().charAt(0),optionInt1.longForm());
		cmd.addOption(optionLong1);
		try {
			cmd.parse(arg1);
		} catch (CMD.OptionException e) {
			//e.printStackTrace();
			assertEquals("Illegal option: '-i-l', 'i' requires a value", e.getMessage());
		}
	}
	
	@Test
	public void test6() {
		CMD cmd = new CMD();
		CMD.Option.IntegerOption optionInt1 = new CMD.Option.IntegerOption('i', "test1");
		CMD.Option.IntegerOption optionInt2 = new CMD.Option.IntegerOption("test2");
		CMD.Option.LongOption optionLong1 = new CMD.Option.LongOption('l', "test3");
		CMD.Option.BooleanOption optionBoolean1 = new CMD.Option.BooleanOption('b', "test9");
		String[] arg1 = {"-bj"};
		cmd.addIntegerOption(optionInt2.longForm());
		cmd.addIntegerOption(optionInt1.shortForm().charAt(0),optionInt1.longForm());
		cmd.addOption(optionBoolean1);
		try {
			cmd.parse(arg1);
		}catch (CMD.UnknownSuboptionException u){
			assertEquals("Illegal option: 'j' in '-bj'", u.getMessage());
			assertEquals('j', u.getSuboption());
		}
		catch (CMD.OptionException e) {
			//e.printStackTrace();
		}
	}

}

