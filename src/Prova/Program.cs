using System;
using System.Reflection;

namespace Prova
{

    internal class Program
    {

        internal static string GetAssemblyAttribute<T>(Assembly asm) where T : Attribute
        {
            var t = typeof(T);
            try
            {
                var rex = new System.Text.RegularExpressions.Regex("(System.Reflection.Assembly)(\\w+)(Attribute)");
                var name = rex.Match(t.FullName).Groups[2].Value;
                var atts = asm.GetCustomAttributes(t, false);
                var att = atts[0] as T;
                var prop = att.GetType().GetProperty(name);
                return prop.GetValue(att).ToString();
            }
            catch (Exception)
            {
                return String.Format("<Undefined Attribute: {0}", t.Name);
            }
        }

        internal static void PrintAllAttributes(Assembly assembly)
        {
            foreach (CustomAttributeData attributedata in assembly.CustomAttributes)
            {
                Console.WriteLine(" Name : {0}", attributedata.AttributeType.Name);
                foreach (CustomAttributeTypedArgument argumentset in attributedata.ConstructorArguments)
                {
                    Console.WriteLine("   >> Value : {0} \n", argumentset.Value);
                }
            }
        }

        static void Main(string[] args)
        {
            var asm = Assembly.GetEntryAssembly();  //(typeof(Lw.Core.Absyn.Ast.Aux));
            string company = GetAssemblyAttribute<AssemblyCompanyAttribute>(asm);
            PrintAllAttributes(asm);
            var product = asm.GetCustomAttribute<AssemblyProductAttribute>();
            Console.WriteLine("asm = {0}\ncompany = {1}\nproduct = {2}\n", asm, company, product.Product);
        }
    }
}
