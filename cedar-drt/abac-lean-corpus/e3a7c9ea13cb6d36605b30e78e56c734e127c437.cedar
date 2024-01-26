@Mlb0233("")
forbid(
  principal == a::"",
  action,
  resource is a in a::"jjjj,jijjjjjjjj\t\0\0\0jjjj\0\0\0@j"
) when {
  (true && resource) && a::""
};
