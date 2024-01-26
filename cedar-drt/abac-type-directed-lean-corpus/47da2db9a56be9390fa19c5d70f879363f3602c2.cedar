forbid(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  ((true && ({"\0\0&": false}["\0\0&"])) && false) && false
};
