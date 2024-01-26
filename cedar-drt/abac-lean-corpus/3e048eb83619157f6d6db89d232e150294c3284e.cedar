@A("&jj-jjj\0\0\0\0jjjjjjijjjjj")
@r("")
permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && (([true, a::"", context].containsAll(a::"jjj")) == a::"jjj")) && a::"jjj"
};
