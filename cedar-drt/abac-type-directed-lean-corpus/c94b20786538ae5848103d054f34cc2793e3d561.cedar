permit(
  principal,
  action,
  resource == a::"\0\0\0\0\0\0\0\0\0"
) when {
  ((true && (if (action in action) then false else (action in action))) && true) && (action in action)
};
