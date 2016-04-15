//          Copyright Alexey Gerasimov(fan-tom) 2016.
// Distributed under the Boost Software License, Version 1.0.
//    (See accompanying file LICENSE_1_0.txt or copy at
//          http://www.boost.org/LICENSE_1_0.txt)
//
// Struct ModInt represents number that is reminder of division on the module,
// which is also stored in structure.
// All operations are available, some of tnem are done using special methods,
// which do these operation more effective,
// such as fast multiplying and exponentiation

module modular;

import std.traits;
import std.conv;
import std.math;

// Exception thrown when operation cannot be done due to different modules
// of arguments
class ModulesAreNotTheSame:Exception{
	this(string mes){
		super(mes);
	}
}

// Function that implements mathematic modulo division in opposite to native
// D's '%' operator; particulary -1%4==-1 while -1.mod(4)==3. In other words
// the result of a%b always satisfies 0<=a%b<|b|
auto mod(D1, D2)(D1 divident, D2 divider) if(is(typeof(D1.init%D2.init)) && is(typeof(abs(D2.init))) && is(typeof(abs(D2.init)+D1.init%D2.init)))
in {
	assert(divider!=0, "Division by zero");
}
out(result) {
	assert(result>=0 && result<divider.abs, result.text);
}
body {
	auto absdiv=divider.abs;
	return (absdiv+divident%absdiv)%absdiv;
}
unittest {
	assert(15.mod(11)==4);
	assert((-1).mod(4)==3);
	assert((-5).mod(-4)==3);
	import std.bigint;
	assert(BigInt("-200").mod(5)==0);
	assert(BigInt(-11).mod(-8)==5);
}

struct ModInt(V, M) if(is(typeof(V.init%M.init)))
{
	private:
		V value_;
		M module_;
		//bool _infinite=false;

		auto inverse() const {
			auto gcd() const {
				static if(is(typeof({ V v=M.init; })))
				//V can be assigned from M
					alias CommonType=V;
				else if(is(typeof({ M m=V.init; })))
				//M can be assigned from V
					alias CommonType=M;
				else 
					static assert(false, "No common type for "~V.stringof~" and "~M.stringof);

				CommonType a=value, r, xn=1, yn=0, yn_, b=mod;
				while(a*b>0){
					r=b%a;
					yn_=yn;
					yn=xn;
					xn=yn_-b/a*xn;
					b=a;
					a=r;
				}
				if(b==1)
					return yn>=0?yn:mod+yn;
				throw new Error(text("Cannot calculate inverse for ",value," modulo ",mod));
			}
			return ModInt!(V,M)(gcd(),mod);
		}

		///Check if modules are the same
		///
		/// Params:
		///
		/// M1 =
		/// M2 =
		auto checkMod(M1, M2)(M1 m1, M2 m2) const pure
		{
			return m1==m2;
		}

	public:

		//getter
		@property auto value() const pure nothrow
		{
			return value_;
		}
		
		//setter
		@property auto value(T)(T val_) nothrow
		{
			value_=val_;
		}

		//getter
		@property auto mod() const pure nothrow
		{
			return module_;
		}

		//setter
		@property auto mod(T)(T mod_) nothrow
		{
			module_=mod_;
		}

		//What can be reasonable init value for value_ and especially for module_?
		@disable this();

		this(in V val_, in M mod_){
			module_=mod_;
			value_=val_.mod(mod_);//(val_>=0?val_%mod:(mod-(-val_%mod)));
		}
		/*static  auto infinity(){
			return new ModInt();
		}*/
		/*@property const pure bool infinite(){
			return _infinite;
		}*/
		const auto opBinary(string op, T)(in T rhs) if((op=="+" || op=="*" || op=="-") && isIntegral!(T))
		out(result){
			assert(result.value<result.mod,text(value,op,rhs,'=',result.value));
		}
		body{
			/*if(infinite)
				return infinity();*/
			return ModInt(mixin("value"~op~"rhs"),mod);
		}
		const auto opBinary(string op, T)(in T rhs) if((op=="+" || op=="*" || op=="-") && is(T: ModInt))
		out(result){
			/*if(infinite || rhs.infinite)
				assert(result.infinite,text(this.value,op,rhs.value,'=',result.value," mod ",result.mod));
			else*/
				assert(result.value<result.mod,text(this.value,op,rhs.value,'=',result.value," mod ",result.mod));
		}
		body{
			/*if(infinite || rhs.infinite)
				return infinity();*/
			if(mod==rhs.mod){
				return ModInt(mixin("value"~op~"rhs.value"),mod);
			}
			throw new ModulesNotTheSame("Operands have different modiles: "~mod.to!string~" and "~rhs.mod.to!string);
		}
		const auto opBinary(string op, T)(in T rhs) if((op=="/") && is(T: ModInt))
		out(result){
			if(rhs.value)
				assert(result.value<result.mod && result.value<result.mod);
			else
				assert(result.infinite);
		}
		body{
			/*if(rhs.value==0)
				return ModInt.infinity();*/
			return this*rhs.inverse;
		}
}
unittest{
	auto a=ModInt!(int,int)(10,4);
	assert(a.value==10%4);
	assert(a.mod==4);
	auto b=a+3;
	assert(b.value==(3+10%4)%4);
	assert(b.mod==4);
	assert(( a/b ).value==2);
}

// Factory function to avoid explicit type indication using IFTI
auto modint(V, M)(V value, M mod){
	return ModInt!(V,M)(value,mod);
}
unittest{
	auto a=modint(10,4);
	assert(a.value==10%4);
	assert(a.mod==4);
	auto b=a+3;
	assert(b.value==(3+10%4)%4);
	assert(b.mod==4);
	import std.bigint;
	auto bigi=modint(BigInt("100"),3);
	assert(bigi.value==1);
	assert(bigi.mod==3);
}
