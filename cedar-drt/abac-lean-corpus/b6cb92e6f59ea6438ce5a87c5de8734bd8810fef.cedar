permit(
  principal == a::"j",
  action == Action::"",
  resource == a::"j"
) when {
  true && ((!false) == (a::"j" == action))
};
