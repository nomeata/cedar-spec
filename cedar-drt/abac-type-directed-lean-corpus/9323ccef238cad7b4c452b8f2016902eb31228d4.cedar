permit(
  principal == a::"\0&o",
  action,
  resource == a::"\0&o"
) when {
  (true && (a::"\0&o" is a)) && true
};
