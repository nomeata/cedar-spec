@A("&jj-jjj\0\0\0\0jjjjjjijjjjj")
@r("")
permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && (([true, Action::"action", false].containsAll(a::"jjj" in (-1))) == a::"jjj")) && true
};
