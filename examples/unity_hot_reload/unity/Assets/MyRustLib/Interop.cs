// Automatically generated by Interoptopus.

#pragma warning disable 0105
using System;
using System.Collections;
using System.Collections.Generic;
using System.Runtime.InteropServices;
using My.Company;
#pragma warning restore 0105

namespace My.Company
{
    public static partial class InteropClass
    {
        public const string NativeLib = "unity_hot_reload";

        static InteropClass()
        {
        }


        [LibraryImport(NativeLib, EntryPoint = "do_math")]
        public static partial uint do_math(uint x);

    }



}
