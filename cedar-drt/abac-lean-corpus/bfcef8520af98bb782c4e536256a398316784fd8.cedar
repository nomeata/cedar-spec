@G("")
permit(
  principal == a::"dddd\0\0jj",
  action in [Action::"                             ",Action::"",Action::"                             "],
  resource is a in a::""
) when {
  true
};
